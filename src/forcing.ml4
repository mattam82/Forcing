(* -*- compile-command: "make -k -C .. src/unicoq_plugin.cma src/unicoq_plugin.cmxs" -*- *)
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

let name s = Name (id_of_string "s")
let coq_proj1_sig = lazy (Coqlib.coq_constant "proj1_sig" ["Init";"Specif"] "proj1_sig")
let coq_exist = lazy (Coqlib.coq_constant "exist" ["Init";"Specif"] "exist")
let coq_sig = lazy (Coqlib.coq_constant "sig" ["Init";"Specif"] "sig")

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
    mkApp (Lazy.force coq_sheaf, [| p |])
      
  let sheafC p =
    mkApp (Lazy.force coq_sheafC, [| p |])
      
  let subp p = 
    mkApp (Lazy.force coq_subp, [| p |])
      
  let cond_pred y = 
    mkLambda (name "x", mkApp (condition_order, [| x; lift 1 y |]))
      
  let sP p q = 
    mkApp (Lazy.force coq_proj1_sig, [|condition_type; cond_pred p; q|])

  let newevar evars env ty = 
    Evarutil.new_evar evars env ty

  type 'a term = env -> evar_map -> 'a * evar_map

  let mk_prod na t b : constr term = fun env sigma ->
    let t', sigma = t env sigma in
    let b', sigma = b ((na, None, t') :: env) sigma in
      mkProd (na, t', b'), sigma

  let mk_lam na t b : constr term = fun env sigma ->
    let t', sigma = t env sigma in
    let b', sigma = b ((na, None, t') :: env) sigma in
      mkLambda (na, t', b'), sigma

  let lookup_rel na env = 
    list_try_find_i (fun i (na', b, t as tup) ->
		       if na = na' then (i, tup) else raise (Failure "not found"))
      1 env

  let mk_var s : constr term = fun env sigma ->
    let (n, _) = lookup_rel (name s) env in mkRel n, sigma

  let mk_evar ty : constr term = fun env sigma ->
    let sigma', ev = newevar sigma env ty in
      ev, sigma'

  let bind (x : 'a term) (f : 'a -> 'b term) : 'b term = fun env sigma ->
    let x', sigma = x env sigma in
      f x' env sigma

  let mk_hole : constr term = 
    bind (newevar (new_Type ())) mk_evar

  let return (t : 'a) : 'a term = fun _ sigma -> t, sigma

  let eval_term (t : 'a term) (e : env) (s : evar_map) : 'a * evar_map =
    t e s

  let mk_app t us : constr term = fun env sigma ->
    let t', sigma = t env sigma in
    let us', sigma = 
      List.fold_left (fun (sigma, args) arg ->
			let arg', sigma = arg env sigma in
			  sigma, arg' :: args)
	(sigma, []) 
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
      mk_prod na t (fun env evars -> b sigma' env evars)

  let mk_var_prod na t cond b = fun sigma env evars ->
    let sigma' = (t, mkRel 1, cond) :: lift_sigma sigma in
      mk_prod na t (fun env evars -> b sigma' env evars)

  let mk_cond_lan na t b = fun sigma env evars ->
    let sigma' = lift_sigma sigma in
      mk_lam na t (fun env evars -> b sigma' env evars)

  let mk_var_lam na t cond b = fun sigma env evars ->
    let sigma' = (t, mkRel 1, cond) :: lift_sigma sigma in
      mk_lam na t (fun env evars -> b sigma' env evars)

  let bind_forcing (x : 'a forcing_term) (f : 'a -> 'b forcing_term) : 'b forcing_term =
    fun sigma env evars ->
      bind (x sigma) (fun x sigma env evars -> f x sigma env evars)
	
  let return_forcing (x : 'a) : 'a forcing_term = fun _ _ evars -> x, evars

  let comm_pi m t' u' p =
    mk_prod (name "r") (subp p)
      (mk_prod (name "s") (subp (mk_var "r"))
	 (mk_prod (name "N") t'
	    (mk_appc (Lazy.force coq_eq)
	       [ mk_hole; 
		 mk_app m [mk_var "s"; 
			   mk_app (return (lift 2 (snd t'))) [mk_var "r"; mk_var "s"; mk_var "N"]];
		 mk_app u' (m :: [mk_var "r"; mk_var "N"]) ]
	    )
	 )
      )
      


  let rec trans (c : constr) (p : condition term) : (constr * constr) forcing_term =
    let interp c p = bind_forcing (trans c p) (fun (x, y) -> return_forcing x) in
    let restriction c p = bind_forcing (trans c p) (fun (x, y) -> return_forcing y) in

    match kind_of_term c with

    | Sort s -> 
	let fst = mk_cond_lam (name "q") (mk_appc subp [p]) 
	  (mk_appc sheaf [mk_var "q"]) 
	in
	let snd = mk_appc sheafC [p] in
	  bind fst (fun x -> bind snd (fun y -> return (x, y)))

(*     | Prod (na, t, u) - *)
(* 	let t' = trans t (mk_var "r") in *)
(* 	let u' = trans u (mk_var "r") in *)
(* 	let fty = mk_cond_prod (name "r") (mk_appc subp [mk_var "q"]) *)
(* 	  (mk_var_prod (name "x") (interp t (mk_var "r")) (mk_var "r") *)
(* 	     (interp u (mk_var "r"))) *)
(* 	in *)
(* 	let ty = *)
(* 	  mk_cond_lam (name "q") (mk_appc subp [p]) *)
(* 	    (mk_appc coq_sig [fty; *)
(* 			      mk_var_lam (name "f") fty (comm_pi (mkRel 1) t' u' (mk_var "q"))]) *)
(* 	in *)
(* 	let value =  *)
(* 	  mkLambda (name "q", subp p,  *)
(* 		    mkLambda (name "r", subp (sP (lift 1 p) (mkRel 1)), *)
(* 			      mkLambda (name "f", ty, *)
(* 					mkLambda (name "s", subp (sP (sP (lift 3 p) (mkRel 3)) (mkRel 2)), *)
(* 						  mkApp (mkRel 2, [| mkRel 1 |]))))) *)
(* 	in ty, value *)

    | Rel n -> fun sigma -> 
	let (var, ty, cond) = List.nth sigma (pred n) in
	let restrict = restriction ty (return cond) in
	  (mk_app restrict (return var))

    | App (m, ns) -> assert false
    | _ -> assert false

end

(*		  
  let rec trans (c : constr) (p : condition) (sigma : env) : constr * constr =
    match kind_of_term c with
    | Sort s -> (mkLambda (name "q", subp p, sheaf (sP (lift 1 p) (mkRel 1))),
		 sheafC p)
    | Prod (na, t, u) -> 
	let t' = trans t (mkRel 1) (* r *) sigma in
	let u' = trans u r ((t, mkRel 2 (* r *)) :: sigma) in
	let fty = mkProd (name "r", subp (sP (lift 1 p) (mkRel 1)),
			  mkProd (name "x", fst t', fst u'))
	in
	let ty =
	  mkLambda (name "q", subp p,
		    mkApp (coq_sig, fty, 
			   mkLambda (name "f", fty, comm_pi (mkRel 1) t t' u u' (sP (lift 2 p) (mkRel 2)))))
	in
	let value = 
	  mkLambda (name "q", subp p, 
		    mkLambda (name "r", subp (sP (lift 1 p) (mkRel 1)),
			      mkLambda (name "f", ty,
					mkLambda (name "s", subp (sP (sP (lift 3 p) (mkRel 3)) (mkRel 2)),
						  mkApp (mkRel 2, [| mkRel 1 |])))))
	in ty, value

    | Rel n -> let (ty, cond) = List.nth sigma (pred n) in
	let restrict = snd (trans ty cond sigma) in
	  (mkApp (restrict, [| mkRel n |])

    | App (m, ns) ->
	
	
			   
			   
*)
