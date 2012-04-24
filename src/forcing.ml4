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
	 iter_body (fun c -> check_term env evd c t) b;
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

let coq_eq_rect = lazy (Coqlib.coq_constant "eq" ["Init";"Logic"] "eq_rect")
let coq_identity = lazy (Coqlib.coq_constant "eq" ["Init";"Datatypes"] "identity")

let coq_sum = lazy (Coqlib.coq_constant "sum" ["Init";"Specif"] "sigT")
let coq_dep_pair = lazy (Coqlib.coq_constant "sum" ["Init";"Specif"] "existT")
let coq_pi1 = lazy (Coqlib.coq_constant "sum" ["Init";"Specif"] "projT1")
let coq_pi2 = lazy (Coqlib.coq_constant "sum" ["Init";"Specif"] "projT2")

let init_reference = Coqlib.find_reference "Forcing"
let init_constant mods reference = constr_of_global (init_reference mods reference)

let forcing_constant c = lazy (init_constant ["Forcing";"Init"] c)
let coq_nondep_prod = forcing_constant "prodT"
let coq_nondep_pair = forcing_constant "pairT"

let coq_eqtype = forcing_constant "eq_type"
let coq_eqtype_ref = lazy (init_reference ["Forcing";"Init"] "eq_type")

let coq_app = forcing_constant "app_annot"
let coq_conv = forcing_constant "conv_annot"
let coq_forcing_op = lazy (init_reference ["Forcing";"Init"] "ForcingOp")
let coq_forcing_op_type = forcing_constant "forcing_traduction_type"
let coq_forcing_op_trad = forcing_constant "forcing_traduction"

module type ForcingCond = sig
  val cond_mod : string list
  val condition_type : types
  val condition_order : constr
end

module Forcing(F : ForcingCond) = struct
  open F

  let forcing_const = init_constant cond_mod

  let coq_subp = forcing_const "subp"

  let coq_ssubp = forcing_const "ssubp"

  let coq_subp_proj = forcing_const "subp_proj"
      
  let coq_sheaf = forcing_const "sheaf"
      
  let coq_sheafC = forcing_const "sheafC"

  let coq_transport = forcing_const "transport"

  let coq_iota = forcing_const "iota"

  let coq_iota_refl = forcing_const "iota_refl"

  let forcing_class = Typeclasses.class_info (Lazy.force coq_forcing_op)

  let find_forcing_op c =
    let ty = Typing.type_of (Global.env ()) Evd.empty c in
    let impl = constr_of_global forcing_class.Typeclasses.cl_impl in
    let cstr = mkApp (impl, [| ty ; c |]) in
    let (_, inst) = Typeclasses.resolve_one_typeclass (Global.env ()) Evd.empty cstr in
    let proj f = mkApp (f, [| ty; c; inst |]) in
      (proj (Lazy.force coq_forcing_op_type),
       proj (Lazy.force coq_forcing_op_trad))
      
  let sheaf p =
    mkApp (coq_sheaf, [| p |])
      
  let sheafC p =
    mkApp (coq_sheafC, [| p |])
      
  let subp p = 
    mkApp (coq_subp, [| p |])

  let ssubp p q = 
    mkApp (coq_ssubp, [| p; q |])

  let cond_pred y = 
    mkLambda (name "x", condition_type, mkApp (condition_order, [| mkRel 1; lift 1 y |]))
      
  let sP p q = mkApp (coq_subp_proj, [| p; q |])

  let newevar ty env evars = 
    Evarutil.new_evar evars env ty

  let lookup_rel na env =
    try 
      list_try_find_i (fun i (na', b, t as tup) ->
		       if na = na' then (i, tup) else raise (Failure "not found"))
      1 env
    with Failure _ -> raise Not_found
	
  type condition = constr

  (* Variables environment: the translated variable index, translated type and 
     condition index if not a condition variable *)
  type env = (name * types * condition option) list

  type 'a forcing_term = env -> 'a

  let bind (x : 'a forcing_term) (f : 'a -> 'b forcing_term) : 'b forcing_term =
    fun sigma -> let y = x sigma in f y sigma
	
  let return (x : 'a) : 'a forcing_term = fun _ -> x

  let mk_var s = fun sigma -> mkVar s

  let mk_app t us = fun sigma ->
    let t' = t sigma in
    let us' = List.map (fun t -> t sigma) us in
      mkApp (t', Array.of_list us')

  let mk_appc t us = mk_app (return t) us

  let ty_hole = new_meta ()
  let hole = new_meta ()

  let mk_hole sigma = mkMeta hole
  let mk_ty_hole sigma = mkMeta ty_hole

  let array_dropn n a =
    Array.sub a n (Array.length a - n)

  let rec simplc c =
    match kind_of_term c with
    | App (f, args) when isLambda f ->
      let (na, _, body) = destLambda f in
      let s' = subst1 args.(0) (subst_var (out_name na) body) in
	simplc (mkApp (s', array_tl args))
    | App (f, args) when f = Lazy.force coq_exist && Array.length args > 4 ->
      simplc (mkApp (args.(2), array_dropn 4 args))
    | _ -> c

  let simpl c sigma =
    simplc (c sigma)

  let reduce_fn c =
    let env = Global.env () and evd = Evd.empty in
      Tacred.simpl env evd c

  let iota p = mk_appc coq_iota [mk_hole; p; mk_hole; mk_hole]
  let iota_refl p = mk_appc coq_iota_refl [p]

  let interp tr p = 
    let rec term tr = 
      match kind_of_term (simplc tr) with
      | App (f, args) when f = Lazy.force coq_dep_pair || f = Lazy.force coq_nondep_pair ->
	return (simplc args.(2))
      | _ ->
	mk_appc (Lazy.force coq_pi1) [mk_ty_hole; mk_ty_hole; simpl (return tr)]
    in simpl (mk_app (term tr) [p])

  let restriction tr p q = 
    let rec term tr = 
      match kind_of_term (simplc tr) with
      | App (f, args) when f = Lazy.force coq_dep_pair || f = Lazy.force coq_nondep_pair ->
	return (simplc args.(3))
      | _ ->
	mk_appc (Lazy.force coq_pi2) [mk_ty_hole; mk_ty_hole; simpl (return tr)]
    in simpl (mk_app (term tr) [iota p; iota q])

  let mk_cond_abs abs na t b = fun sigma ->
    let t' = t sigma in
    let sigma' = (Name na, t', None) :: sigma in
      abs (Name na, t', b sigma')
    
  let mk_var_abs abs na t' cond b sigma =
    let t' = interp t' (return cond) sigma in
    let sigma' = (Name na, t', Some cond) :: sigma in
      abs (Name na, t', b sigma')

  let mk_cond_prod = mk_cond_abs mkProd
  let mk_var_prod = mk_var_abs mkProd
  let mk_cond_lam = mk_cond_abs mkLambda
  let mk_var_lam = mk_var_abs mkLambda

  let mk_let na c t b = fun sigma ->
    mkLetIn (Name na, c sigma, t sigma, b sigma)

  let subpt p = 
    mk_appc coq_subp [p]

  let ssubpt p q = 
    mk_appc coq_ssubp [p; q]

  let var_of = function Name id -> fun _ -> mkVar id | Anonymous -> assert false

  let build_ident s =
    let r = ref 0 in
    let id = id_of_string s in
      (fun () -> r := 0), 
      (fun () -> let id' = if !r = 0 then id else add_suffix id (string_of_int !r) in
	 incr r; id')

  let clear_p, next_p = build_ident "p"
  let clear_q, next_q = build_ident "q"
  let clear_r, next_r = build_ident "r"
  let clear_s, next_s = build_ident "s"
  let clear_f, next_f = build_ident "f"
  let clear_ty, next_ty = build_ident "ty"
  let clear_prop, next_prop = build_ident "prop"
  let clear_anon, next_anon = build_ident "arg"

  let var id = fun sigma -> mkVar id

  let comm_pi m na rn t' sn u' p =
    mk_cond_prod rn (subpt p)
    (mk_cond_prod sn (subpt (mk_var rn))
     (mk_var_prod na t' (iota (mk_var rn) [])
      (mk_appc (Lazy.force coq_eq)
       [ mk_ty_hole; (* mk_ty_hole; mk_hole; *)
	 simpl (mk_app (restriction u' (mk_var rn) (mk_var sn)) 
		[mk_app m [mk_var rn; mk_var na]]);
	 mk_app m [iota (mk_var sn); 
		   simpl (mk_app (restriction t' (mk_var rn) (mk_var sn)) [mk_var na])];
       ]
      )
     )
    )
    
  let mk_pair a b : constr forcing_term =
    mk_appc (Lazy.force coq_nondep_pair) [mk_ty_hole; mk_ty_hole; a; b]

  let mk_dep_pair a b : constr forcing_term =
    mk_appc (Lazy.force coq_dep_pair) [mk_ty_hole; mk_ty_hole; a; b]

  let mk_sheaf_pair p a b : constr forcing_term =
    mk_appc (Lazy.force coq_dep_pair) 
    [return (mkProd (Anonymous, mkApp (coq_subp, [| p |]), new_Type ()));
     mk_appc coq_transport [return p]; a; b]

  let rec find_rel sigma n =
    match sigma, n with
    | (x, y, Some cond) :: _, 0 -> (x, y, cond)
    | (x, y, Some cond) :: tl, n -> find_rel tl (pred n)
    | (_, _, None) :: tl, n -> find_rel tl n
    | [], _ -> assert false
      

  let abstract t sigma =
    let free = global_vars_set (Global.env ()) t in
    let abs, vars, _ = 
      List.fold_left 
        (fun (c, vars, free) (na, ty, cond) ->
	 let id = out_name na in
	   if Idset.mem id free then
	     let ty' = match cond with
	       | None -> ty
	       | Some cond -> interp ty (return cond) sigma
	     in 
	     let ids' =
	       Idset.union (global_vars_set (Global.env ()) ty')
	       (Idset.add id free)
	     in
	       mkLambda (na, ty', c), (id :: vars), ids'
	   else c, vars, free)
      (t, [], free) sigma
    in vars, abs
      
  let defs = ref []

  let remember name ty = 
    let memo = ref false in
      fun sigma -> 
        if !memo then 
	  let (body, inst) = List.assoc name !defs in inst
	else
	  let vars, abs = abstract (ty sigma) sigma in
	  let inst = mkApp (mkVar name, Array.of_list (List.map mkVar vars)) in
	    defs := (name, (abs, inst)) :: !defs;
	    memo := true;
	    inst

  let rec trans (c : constr) (p : constr) : constr forcing_term =
    let trans c p = simpl (trans c p) in
    let pc = return p in
    let interpretation c p sigma = interp (trans c p sigma) (iota (return p)) sigma in
    let trivial c =
      let term = mk_cond_lam (next_q ()) (mk_appc coq_subp [pc]) (return c) in
      let restr = 
	let qn = next_q () and rn = next_r () and sn = next_s () in
	  mk_cond_lam qn (mk_appc coq_subp [pc])
	  (mk_cond_lam rn (mk_appc coq_subp [mk_var qn])
	   (mk_cond_lam sn (mk_appc coq_subp [mk_var rn])
	    (mk_var sn))) 
      in (mk_pair term restr)
    in
      match kind_of_term c with
      | Sort s -> 
	let q = next_q () in 
	let fst = mk_cond_lam q (subpt pc) 
	  (mk_appc coq_sheaf [var q])
	in
	let snd = mk_appc coq_sheafC [pc] in
	  (mk_sheaf_pair p fst snd)

      | Prod (na, t, u) -> 
	let na = next_anon () in
	let rn = next_r () and qn = next_q () and fn = next_f () and sn = next_s () in
	let prod sigma =
	  let r = mk_var rn sigma in
	  let sigmar = (Name rn, (mk_appc coq_subp [mk_var qn] sigma), None) ::
	    (Name qn, (mk_appc coq_subp [pc] sigma), None) ::
	    sigma
	  in
	  let t' = remember (next_ty ()) (trans t (mkVar rn)) sigmar in
	  let u' = remember (next_ty ()) (trans u (mkVar rn)) ((Name na, t', Some r) :: sigmar) in
	  let fty = 
 	    mk_cond_prod rn (mk_appc coq_subp [mk_var qn])
	    (mk_var_prod na t' r (interp u' (mk_var rn)))
	  in
	  let ftyrem = remember (next_ty ()) fty in
	  let ftyprop = 
	    let prop = mk_cond_lam fn ftyrem (comm_pi (mk_var fn) na rn t' sn u' (mk_var qn)) in
	      remember (next_prop ()) prop
	  in
	  let ty =
	    (mk_cond_lam qn (mk_appc coq_subp [pc])
	     (mk_appc (Lazy.force coq_sig)
	      [ftyrem;
	       ftyprop]))
	  in
	  let value =
	    let qn' = next_q () in
	    let rn' = next_r () in
	      mk_cond_lam qn' (mk_appc coq_subp [pc])
	      (mk_cond_lam rn' (mk_appc coq_subp [mk_var qn'])
	       (mk_cond_lam fn (simpl (mk_app ty [mk_var qn']))
		(mk_cond_lam sn (mk_appc coq_subp [mk_var rn'])
		 (mk_app (mk_var fn) [mk_var sn]))))
	  in 
	    (mk_sheaf_pair p ty value) sigma
	in prod

      | Lambda (na, t, u) -> 
	let l sigma =
	  let na = if na = Anonymous then next_anon () else out_name na in
	  let qn = next_q () in
	  let t' = trans t (mkVar qn) sigma in
	  let term =
	    mk_cond_lam qn (mk_appc coq_subp [pc])
	    (mk_var_lam na (interp t' (mk_var qn) sigma) (mkVar qn)
	     (trans u (mkVar qn)))
	  in term sigma
	in l

	  
      | Rel n -> 
	(fun sigma -> 
	 let (var, tr, cond) = find_rel sigma (pred n) in
	 let restrict = restriction tr (fun sigma -> cond) pc in
  	   (simpl (mk_app restrict [return (mkVar (out_name var))]) sigma))

      | App (f, args) when f = Lazy.force coq_app -> 
	let fty = args.(1) and n = args.(2) and m = args.(3) in
	let na, t, u = destLambda fty in
	let uxn = interpretation (subst1 n u) p in
	let u sigma = 
	  let sigma' = ((na, t, Some (pc sigma)) :: sigma) in
	    interp (trans u p sigma') pc sigma' 
	in
	let np = trans n p in
	  (mk_appc (Lazy.force coq_eq_rect)
	   [uxn; mk_appc (Lazy.force coq_identity) [mk_hole]; 
	    (fun sigma -> replace_vars [out_name na, np sigma] (u sigma));
	    mk_hole; trans m p])
	  
      | App (f, args) when f = Lazy.force coq_conv -> 
	let t = args.(0) and u = args.(1) and m = args.(2) in
	  (mk_appc (Lazy.force coq_eq_rect)
	   [interpretation u p; return (Lazy.force coq_identity); 
	    interpretation t p; mk_hole; trans m p])
	
      | App (f, args) when f = Lazy.force coq_sum -> assert false

      | App (f, args) -> 
	(mk_app (trans f p) (iota_refl pc :: List.map (fun x -> trans x p) (Array.to_list args)))

      | Const cst ->
	(try 
	   let env = Global.env () in
	   let cty = type_of_constant env cst in
	   let ty = mkApp (constr_of_global forcing_class.Typeclasses.cl_impl, [| cty; c |]) in
	   let evars, impl = Typeclasses.resolve_one_typeclass env Evd.empty ty in
	     (return (whd_betadeltaiota env Evd.empty
		      (mkApp (constr_of_global
			      (Nametab.global (Ident (dummy_loc, id_of_string "forcing_traduction"))),
			      [| cty; c; impl; p |]))))
	 with Not_found -> trivial c)

      | _ -> trivial c

  let named_to_nameless env subst c =
    let rec aux env c = 
      match kind_of_term c with
      | Meta _ -> c
      | Var id -> 
	(try
	   let i, _ = lookup_rel (Name id) (rel_context env) in
	     mkRel i
	 with Not_found -> 
	   try List.assoc id subst
	   with Not_found -> c)
      | _ ->
	map_constr_with_full_binders (fun decl env -> push_rel decl env) aux env c
    in 
    let c' = aux env c in
      c'

  let rec meta_to_holes gc =
    match gc with
    | Glob_term.GEvar (loc, ek, args) -> Glob_term.GHole (loc, Evd.InternalHole)
    | Glob_term.GApp (loc, (Glob_term.GRef (loc', gr) as f), args) when gr = Lazy.force coq_eqtype_ref ->
      let args' = List.map meta_to_holes args in
	(match args' with
	   [a; b; prf; t; u] ->
	   Glob_term.GApp (loc, f,
			   [a; b; prf; Glob_term.GCast (loc, t, Glob_term.CastCoerce);
			    Glob_term.GCast (loc, u, Glob_term.CastCoerce)])
	 | _ -> assert false)
    | c -> Glob_term.map_glob_constr meta_to_holes c

  let interpretation c sigma = 
    let pn = next_p () in let p = mk_var pn in
    let sigma' = (Name pn, condition_type, None) :: sigma in
    let tr _ = trans c (mkVar pn) sigma' in
    let inter = interp (simpl (mk_app tr [p]) sigma') p sigma' in
      mkProd (Name pn, condition_type, inter)


  let interp env evs term = 
    let j, _ = Pretyping.understand_judgment_tcc evs env term in
      j.uj_val, j.uj_type

  let define_aux env name subst body k =
    let c' = named_to_nameless env subst body in
    let dt = Detyping.detype true [] [] c' in
    let dt = meta_to_holes dt in
    let evs = ref Evd.empty in
      Flags.program_mode := true;

    let term, ty = interp env evs dt in
    let term = Tacred.simpl env !evs term in
    let evars, _, def, ty = Obligations.eterm_obligations env name !evs 0 term ty in
      ignore (Obligations.add_definition name ~term:def ?hook:k ty evars)
    
  let translate id tr c env sigma k = 
    defs := [];
    clear_p (); clear_q (); clear_r (); clear_s (); clear_f (); clear_anon (); clear_ty ();
    clear_prop ();
    let c' = tr c [] in
    let hook subst = 
      let c' = named_to_nameless (Global.env ()) subst c' in
      let dt = Detyping.detype true [] [] c' in
      let dt = meta_to_holes dt in
	k dt
    in
    let rec aux subst defs = 
      match defs with 
      | [] -> hook subst
      | (name, (body, _)) :: defs ->
	let newname = add_prefix (string_of_id id) name in
	  define_aux (Global.env ()) newname subst body 
	  (Some (fun _ gr -> 
		 aux ((name, constr_of_global gr) :: subst) defs))
    in aux [] (List.rev !defs)

  (* let tac i c = fun gs -> *)
  (*   let env = pf_env gs and sigma = Refiner.project gs in *)
  (*     translate i trans c env sigma  *)
  (*     (fun term' -> *)
  (*      let evs = ref sigma in *)
  (*      let term'', ty = interp env evs term' in *)
  (* 	 tclTHEN (tclEVARS !evs)  *)
  (* 	 (letin_tac None (Name i) term'' None onConcl) gs) *)

  (** Define [id] as the translation of [c] (with term and restriction map) *)
  let command id tr ?hook c =
    let env = Global.env () and sigma = Evd.empty in
    let c = Constrintern.interp_constr sigma env c in
      translate id tr c env sigma 
      (fun term' ->
       let env = (Global.env ()) in
       let evs = ref sigma in
       let term, ty = interp env evs term' in
       let term = Tacred.simpl env !evs term in
       let evars, _, def, ty = Obligations.eterm_obligations env id !evs 0 term ty in
       let hook = Option.map (fun f -> f c) hook in
	 ignore (Obligations.add_definition id ~term:def ?hook ty evars))
      
  open Decl_kinds
  open Global

  let reference_of_global g = 
    Qualid (dummy_loc, Nametab.shortest_qualid_of_global Idset.empty g)

  let forcing_operator id c =
    let mode = 
      let m = !Flags.program_mode in
	Flags.program_mode := true; m in
    let hook ty _ gr = 
      let env = Global.env () in
      let ax = 
	Declare.declare_constant id (ParameterEntry (None, ty, None), IsAssumption Logical)
      in
      let trty = constr_of_global gr in
      let evars, ev = Evarutil.new_evar Evd.empty env trty in
      let body, types = 
	Typeclasses.instance_constructor forcing_class 
        [ty; mkConst ax; trty; ev]
      in
      let id' = add_suffix id "_inst" in
      let evars, _, def, ty = 
	Obligations.eterm_obligations env id' evars 0 (Option.get body) types 
      in
	ignore (Obligations.add_definition id' ~term:def 
		~hook:(fun loc gr ->
		       Typeclasses.add_instance
		       (Typeclasses.new_instance forcing_class None false gr))
	        ty evars);
	Flags.program_mode := mode
    in command (add_suffix id "_trans") interpretation c ~hook

end


(* For naturals ordered by le *)
  
module NatCond : ForcingCond = struct
  let cond_mod = ["Forcing";"Init";"NatForcing"]
  let condition_type = init_constant ["Coq";"Init";"Datatypes"] "nat" 
  let condition_order = init_constant ["Coq";"Init";"Peano"] "le"
end

module NatForcing = Forcing(NatCond)

(* TACTIC EXTEND nat_forcing *)
(* [ "nat_force" constr(c) "as" ident(i) ] -> [ NatForcing.tac i c ] *)
(* END *)

VERNAC COMMAND EXTEND Forcing_operator
[ "Forcing" "Operator" ident(i) ":" constr(c)  ] -> [ NatForcing.forcing_operator i c ]
END

(* VERNAC COMMAND EXTEND Force *)
(* [ "Force" ident(i) ":=" constr(c)  ] -> [ NatForcing.command i NatForcing.trans c ] *)
(* END *)
