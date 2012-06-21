Require Import Forcing.
Import NatForcing.
Import NatCondition.
Open Scope forcing_scope.

Require Import "fix". 
Require Import eqf_def.

Hint Extern 4 => progress (unfold le in *) : forcing.

Obligation Tactic := program_simpl; forcing.
(* Notation " '{Σ'  x } " := (exist x _). *)

(* Lemma equal_existT_ext {A B} {P : (A -> B) -> Type} {p q : A -> B} {x : P p} {y : P q}  *)
(*   : (forall x : A, p x = q x) -> (forall H : p = q, cast H in x = y) -> *)
(*     existT p x = existT q y. *)
(* Proof. intros. *)
(*   assert (p = q). *)
(*   now extensionality g. *)
(*   subst. f_equal.  apply (H0 eq_refl).  *)
(* Qed. *)

Forcing
Lemma switch_next : (forall A : Type, eqf Type (switch (next _  A)) (later A)).
Next Obligation.
Proof.
  red. intros. red.
  destruct r. simpl.
  intros. 
  red. intros.
  unfold Θ. simpl.
  

  unfold sheafC.
  destruct r as [[|r] Hr].
  simpl.
  refine (equal_existT_ext _ _).
  intros.
  unfold later_trans_sheaf. simpl.
  unfold later_sheaf_f, switch_sheaf_def. simpl.
  destruct x as [[|x] Hx]; simpl. reflexivity. bang.

  intros.
  simpl in *.
  apply cast_exist. 
  refine (@cast_lambda _ _ _ H _ _ _ _ _); intro s.
  refine (@cast_lambda _ _ _ H _ _ _ _ _); intro t.
  destruct s as [[|s] Hs]. unfold Θ. simpl.
  unfold later_transp. 
  destruct t as [[|t] Ht]. unfold Θ. simpl.
  reflexivity.
  simpl. bang.
  simpl.

  reflexivity.


   simpl.
  intros.

  simpl.
  intros.
  destruct arg as [sh tr]. unfold switch_sheaf_def, match_sub_subp. simpl.
  unfold later_sheaf_f. simpl. 
