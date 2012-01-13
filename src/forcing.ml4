(* -*- compile-command: "COQBIN=~/research/coq/git/bin/ make -k -C .. src/forcing_plugin.cma src/forcing_plugin.cmxs" -*- *)
(************************************************************************)
(*  v      *   The Coq Proof Assistant  /  The Coq Development Team     *)
(* <O___,, * CNRS-Ecole Polytechnique-INRIA Futurs-Universite Paris Sud *)
(*   \VV/  **************************************************************)
(*    //   *      This file is distributed under the terms of the       *)
(*         *       GNU Lesser General Public License Version 2.1        *)
(************************************************************************)

(*i camlp4deps: "parsing/grammar.cma" i*)
(*i camlp4use: "pa_extend.cmo" i*)

(* $Id: equations.ml4 11996 2009-03-20 01:22:58Z letouzey $ *)

open Cases
open Util
open Names
open Nameops
open Term
open Termops
open Declarations
open Inductiveops
open Environ
open Sign
open Reductionops
open Typeops
open Type_errors
open Pp
open Proof_type
open Refiner
open Retyping
open Pretype_errors
open Evarutil
open Evarconv
open List
open Libnames
open Topconstr
open Entries
open Evd
open Tacexpr
open Tactics
open Tacticals
open Tacmach

open Forcing_common

(* Debugging infrastructure. *)

let debug = true

let check_term env evd c t =
  Typing.check env evd c t

let check_type env evd t =
  ignore(Typing.sort_of env evd t)
    
let typecheck_rel_context evd ctx =
  let _ =
    List.fold_right
      (fun (na, b, t as rel) env ->
	 check_type env evd t;
	 Option.iter (fun c -> check_term env evd c t) b;
	 push_rel rel env)
      ctx (Global.env ())
  in ()

(** Bindings to Coq *)

let coq_eq = lazy (Coqlib.build_coq_eq ())

let mkEq t x y = 
  mkApp (Lazy.force coq_eq, [| refresh_universes t; x; y |])
    
let mkRefl t x = 
  mkApp ((Coqlib.build_coq_eq_data ()).Coqlib.refl, [| refresh_universes t; x |])

let mkHEq t x u y =
  mkApp (Coqlib.coq_constant "mkHEq" ["Logic";"JMeq"] "JMeq",
	[| refresh_universes t; x; refresh_universes u; y |])
    
let mkHRefl t x =
  mkApp (Coqlib.coq_constant "mkHEq" ["Logic";"JMeq"] "JMeq_refl",
	[| refresh_universes t; x |])

let mk_term_eq env sigma ty t ty' t' =
  if Reductionops.is_conv env sigma ty ty' then
    mkEq ty t t', mkRefl ty' t'
  else
    mkHEq ty t ty' t', mkHRefl ty' t'


let unify env sigma c c' = the_conv_x env c c' sigma

let unify_tac c c' i gl =
  let env = pf_env gl in
  let sigma = project gl in
  let sigma' = unify env sigma c c' in
  let c = nf_evar sigma' c and c' = nf_evar sigma' c' in
  let cty = Typing.type_of env sigma' c in
  let eq = mkCast (mkRefl cty c, DEFAULTcast, mkEq cty c c') in
    tclTHEN (tclEVARS sigma') (pose_proof (Name i) eq) gl
    
TACTIC EXTEND pattern_call
[ "unify" constr(c) constr(c') "as" ident(i) ] -> [ unify_tac c c' i ]
END

let name s = Name (id_of_string s)
let coq_proj1_sig = lazy (Coqlib.coq_constant "proj1_sig" ["Init";"Specif"] "proj1_sig")
let coq_exist = lazy (Coqlib.coq_constant "exist" ["Init";"Specif"] "exist")
let coq_sig = lazy (Coqlib.coq_constant "sig" ["Init";"Specif"] "sig")

let init_constant mods reference = constr_of_global (Coqlib.find_reference "Forcing" mods reference)

module type ForcingCond = sig
  
  val condition_type : types
  val condition_record : constr
  val condition_order : constr

end

module Forcing(F : ForcingCond) = struct
  open F
    
  let condargs = [| condition_type; condition_record |]

  let coq_subp =
    mkApp (init_constant ["Forcing";"Init"] "subp", condargs)
      
  let coq_sheaf =
    mkApp (init_constant ["Forcing";"Init"] "sheaf", condargs)
      
  let coq_sheafC =
    mkApp (init_constant ["Forcing";"Init"] "sheafC", condargs)

  let sheaf p =
    mkApp (coq_sheaf, [| p |])
      
  let sheafC p =
    mkApp (coq_sheafC, [| p |])
      
  let subp p = 
    mkApp (coq_subp, [| p |])
      
  let cond_pred y = 
    mkLambda (name "x", condition_type, mkApp (condition_order, [| mkRel 1; lift 1 y |]))
      
  let sP p q = 
    mkApp (Lazy.force coq_proj1_sig, [|condition_type; cond_pred p; q|])

  let newevar ty env evars = 
    Evarutil.new_evar evars env ty

  type 'a term = env -> evar_map -> 'a * evar_map

  let mk_prod na t b : constr term = fun env sigma ->
    let t', sigma = t env sigma in
    let b', sigma = b (push_rel (na, None, t') env) sigma in
      mkProd (na, t', b'), sigma

  let mk_lam na t b : constr term = fun env sigma ->
    let t', sigma = t env sigma in
    let b', sigma = b (push_rel (na, None, t') env) sigma in
      mkLambda (na, t', b'), sigma

  let lookup_rel na env = 
    list_try_find_i (fun i (na', b, t as tup) ->
		       if na = na' then (i, tup) else raise (Failure "not found"))
      1 env

  let mk_var s : constr term = fun env sigma ->
    let (n, _) = lookup_rel (name s) (rel_context env) in mkRel n, sigma

  let mk_evar ty : constr term = fun env sigma ->
    let sigma', ev = newevar ty env sigma in
      ev, sigma'

  let bind (x : 'a term) (f : 'a -> 'b term) : 'b term = fun env sigma ->
    let x', sigma = x env sigma in
      f x' env sigma

  let mk_hole : constr term = 
    bind (mk_evar (new_Type ())) mk_evar

  let return (t : 'a) : 'a term = fun _ sigma -> t, sigma

  let eval_term (t : 'a term) (e : env) (s : evar_map) : 'a * evar_map =
    t e s

  let mk_app t us : constr term = fun env sigma ->
    let t', sigma = t env sigma in
    let sigma, us' = 
      List.fold_left (fun (sigma, args) arg ->
			let arg', sigma = arg env sigma in
			  sigma, arg' :: args)
	(sigma, []) us
    in
      mkApp (t', Array.of_list (List.rev us')), sigma

  let mk_appc t us = mk_app (return t) us
	
  type condition = constr

  (* Variables environment: the translated variable index, translated type and condition index *)
  type env = (constr * types * condition) list

  type 'a forcing_term = env -> 'a term

  let lift_sigma sigma =
    map (fun (ty, var, cond) -> lift 1 ty, lift 1 var, lift 1 cond) sigma

  let mk_cond_prod na t b = fun sigma env evars ->
    let sigma' = lift_sigma sigma in
      mk_prod na (t sigma) (fun env evars -> b sigma' env evars) env evars

  let mk_var_prod na t t' cond b = fun sigma env evars ->
    let sigma' = (mkRel 1, t, cond) :: lift_sigma sigma in
      mk_prod na (t' sigma) (fun env evars -> b sigma' env evars) env evars

  let mk_cond_lam na t b = fun sigma env evars ->
    let sigma' = lift_sigma sigma in
      mk_lam na (t sigma) (fun env evars -> b sigma' env evars) env evars

  let mk_var_lam na t t' cond b = fun sigma env evars ->
    let sigma' = (mkRel 1, t, cond) :: lift_sigma sigma in
      mk_lam na (t' sigma) (fun env evars -> b sigma' env evars) env evars

  let bind_forcing (x : 'a forcing_term) (f : 'a -> 'b forcing_term) : 'b forcing_term =
    fun sigma env evars ->
      bind (x sigma) (fun x env evars -> f x sigma env evars) env evars
	
  let return_forcing (x : 'a) : 'a forcing_term = fun _ _ evars -> x, evars

  let mk_varf s = fun sigma -> mk_var s

  let mk_appf c us = fun sigma ->
    mk_app (c sigma) (map (fun c -> c sigma) us)

  let mk_holef = fun sigma -> mk_hole

  let project proj m =
    bind_forcing m (fun x -> return_forcing (proj x))
    
  let mk_appcf c us = fun sigma ->
    mk_appf (return_forcing c) us sigma

  let subpt p = 
    mk_appf (return_forcing coq_subp) [p]

  let comm_pi m t t' u' p =
    mk_cond_prod (name "r") (subpt p)
      (mk_cond_prod (name "s") (subpt (mk_varf "r"))
	 (mk_var_prod (name "N") t (project fst t')
	    (mkRel 2)
	    (mk_appf (return_forcing (Lazy.force coq_eq))
	       [ mk_holef; 
		 mk_appf m [mk_varf "s"; 
			    mk_appf (project (fun x -> lift 2 (Option.get (snd x))) t')
			    [mk_varf "r"; mk_varf "s"; mk_varf "N"]];
		 mk_appf (project fst u') (m :: [mk_varf "r"; mk_varf "N"]) ]
	    )
	 )
      )
      

  let rec trans (c : constr) (p : condition forcing_term) : (constr * constr option) forcing_term =
    let interp c p = bind_forcing (trans c p) 
      (fun (x, y) -> 
       match y with None -> return_forcing x
       | Some _ -> 
	 bind_forcing p (fun p ->
			 return_forcing (Reduction.whd_betaiotazeta (mkApp (x, [|p|]))))) in
    let restriction c p q = 
      bind_forcing (trans c p) 
      (fun (x, y) ->
       match y with None -> assert false
       | Some y ->
	 bind_forcing p (fun p ->
			 bind_forcing q (fun q -> 
					 return_forcing (Reduction.whd_betaiotazeta (mkApp (y, [|p; q|]))))))

    in
      
    match kind_of_term c with

    | Sort s -> 
	let fst = mk_cond_lam (name "q") (subpt p) 
	  (fun _ -> mk_appc coq_sheaf [mk_var "q"]) 
	in
	let snd = mk_appcf coq_sheafC [p] in
	  bind_forcing fst (fun x -> bind_forcing snd (fun y -> return_forcing (x, Some y)))

    | Prod (na, t, u) ->      
	let t' = trans t (mk_varf "r") in
	let u' = trans u (mk_varf "r") in
	let fty = mk_cond_prod (name "r") (mk_appcf coq_subp [mk_varf "q"])
	  (mk_var_prod na t (interp t (mk_varf "r")) (mkRel 2)
	     (interp u (mk_varf "r")))
	in
	let ty =
	  mk_cond_lam (name "q") (mk_appcf coq_subp [p])
	  (mk_appf (return_forcing (Lazy.force coq_sig)) 
	   [fty;
	    mk_cond_lam (name "f") fty (comm_pi (mk_varf "f") t t' u' (mk_varf "q"))])
	in
	let value =
	  mk_cond_lam (name "q") (mk_appcf coq_subp [p])
	  (mk_cond_lam (name "r") (mk_appcf coq_subp [mk_varf "q"])
	   (mk_cond_lam (name "f") ty 
	    (mk_cond_lam (name "s") (mk_appcf coq_subp [mk_varf "r"])
	     (mk_appf (mk_varf "f") [mk_varf "s"]))))
	in bind_forcing ty 
	   (fun ty -> bind_forcing value
	    (fun value -> return_forcing (ty, Some value)))

    | Rel n -> fun sigma -> 
	let (var, ty, cond) = List.nth sigma (pred n) in
	let restrict = restriction ty (return_forcing cond) p in
	  bind (mk_app (restrict sigma) [return var])
	    (fun a -> return (a, None))

    | _ -> return_forcing (c, Some mkSet)


  let translate c p env sigma = trans c p [] env sigma

  let tac i c p = fun gs ->
    let env = pf_env gs and sigma = Refiner.project gs in
    let (term', type'), evars = translate c p env sigma in
      tclTHEN (tclEVARS evars) (pose_proof (Name i) term') gs

end


(* For naturals ordered by le *)
  
module NatCond : ForcingCond = struct
  let condition_type = init_constant ["Coq";"Init";"Datatypes"] "nat" 
  let condition_record = init_constant ["Forcing";"Init"] "nat_condition"
  let condition_order = init_constant ["Coq";"Init";"Peano"] "le"
end

module NatForcing = Forcing(NatCond)

TACTIC EXTEND nat_forcing
[ "nat_force" constr(c) "at" constr(p) "as" ident(i) ] -> [ NatForcing.tac i c (NatForcing.return_forcing p) ]
END
