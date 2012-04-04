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

open Retyping
open Pretype_errors
open Evarutil
open Evarconv
open List
open Libnames
open Topconstr
open Entries
open Tacmach
open Tacexpr
open Tactics
open Tacticals
open Decl_kinds

open Coqlib

let ($) f g = fun x -> f (g x)

let proper_tails l = snd (List.fold_right (fun _ (t,ts) -> List.tl t, ts @ [t]) l (l, []))

let list_map_filter_i f l = 
  let rec aux i = function
    | hd :: tl -> 
	(match f i hd with
	| Some x -> x :: aux (succ i) tl
	| None -> aux (succ i) tl)
    | [] -> []
  in aux 0 l


let find_constant contrib dir s =
  constr_of_global (Coqlib.find_reference contrib dir s)

let contrib_name = "Forcing"
let init_constant dir s = find_constant contrib_name dir s
let init_reference dir s = Coqlib.find_reference contrib_name dir s

    
let coq_unit = lazy (init_constant ["Coq";"Init";"Datatypes"] "unit")
let coq_tt = lazy (init_constant ["Coq";"Init";"Datatypes"] "tt")

let coq_prod = lazy (init_constant ["Coq";"Init";"Datatypes"] "prod")
let coq_pair = lazy (init_constant ["Coq";"Init";"Datatypes"] "pair")

let fresh_id_in_env avoid id env =
  Namegen.next_ident_away_in_goal id (avoid@ids_of_named_context (named_context env))

let fresh_id avoid id gl =
  fresh_id_in_env avoid id (pf_env gl)

let coq_eq = Lazy.lazy_from_fun Coqlib.build_coq_eq
let coq_eq_refl = lazy ((Coqlib.build_coq_eq_data ()).Coqlib.refl)

let coq_heq = lazy (Coqlib.coq_constant "mkHEq" ["Logic";"JMeq"] "JMeq")
let coq_heq_refl = lazy (Coqlib.coq_constant "mkHEq" ["Logic";"JMeq"] "JMeq_refl")

let mkEq t x y = 
  mkApp (Lazy.force coq_eq, [| refresh_universes_strict t; x; y |])
    
let mkRefl t x = 
  mkApp (Lazy.force coq_eq_refl, [| refresh_universes_strict t; x |])

let mkHEq t x u y =
  mkApp (Lazy.force coq_heq,
	[| refresh_universes_strict t; x; refresh_universes_strict u; y |])
    
let mkHRefl t x =
  mkApp (Lazy.force coq_heq_refl,
	[| refresh_universes_strict t; x |])

(* Lifting a [rel_context] by [n]. *)

let lift_rel_contextn k n sign =
  let rec liftrec k = function
    | (na,c,t)::sign ->
	(na,map_body (liftn n k) c,liftn n k t)::(liftrec (k-1) sign)
    | [] -> []
  in
  liftrec (rel_context_length sign + k) sign

let lift_context n sign = lift_rel_contextn 0 n sign
