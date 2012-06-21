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
  apply f_equal.
  refine (equal_existT_ext _ _).
  intros.
  unfold later_trans_sheaf. simpl.
  unfold later_sheaf_f, switch_sheaf_def. simpl.
  destruct x0 as [[|x0] Hx0]; simpl. reflexivity. 
  destruct x. bang.
  simpl. reflexivity.

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

  destruct t as [[|t] Ht]. unfold Θ. simpl.
  reflexivity.
  simpl.
  destruct x. bang.

  match goal with
      |- context [ eq_rect _ _ ?fn _ _ ] => set(f:=fn)
  end.
  assert(S t <= S x) by (transitivity (S s); forcing).
  assert(S s <= S x) by (forcing).
  transitivity f. 
  apply (eq_rect_unnecessary (fun ty : subp (S x) -> Type => 
                                ty (inject (S s)) -> ty (inject (S t))) _ _ H f eq_refl). 
  subst f. reflexivity.
Qed.