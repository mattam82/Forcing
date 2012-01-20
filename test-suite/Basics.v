Require Import Forcing.
Require Import RelationClasses.

Definition proj_sub {p : nat} : subp p -> nat :=
  fun x => proj1_sig x.

Coercion ι_refl : subp >-> subp.

Hint Extern 0 (_ = _) => apply ι_ι_refl : forcing.
Hint Extern 0 (_ <= _) => apply reflexivity : forcing. 

Notation " '{Σ' x , y } " := (exist _ x y).
Notation " '(Σ' x , y ) " := (existT _ x y).

Lemma ι_ι_refl {p} (q : subp p) : subp (` q) -> subp (` (ι_refl q)).
Proof. intros. exists (` q). reflexivity. Defined.

Section Test.

  Variable p : nat.

  Hint Extern 1 (` ?x <= _) => apply (proj2_sig (ι x)) : forcing.

  Obligation Tactic := program_simpl; eauto 2 with forcing.

  Force empty at p := (forall X : Set, X).

  Next Obligation. f_equal.
    unfold ι, ι_refl. simpl. pi. Defined.

  Next Obligation. f_equal.
    unfold ι, ι_refl. simpl. pi. Defined.

  Program Definition foo := (projT1 empty p).

  Eval hnf in foo.

  Force identity at p := (forall X : Set, X -> X).

  Notation " 'rewrite' p 'in' x " := (eq_rect _ _ x _ p) (at level 10).

  Next Obligation. f_equal. unfold ι. simpl. pi. Defined.
  Next Obligation. f_equal; unfold ι; simpl; pi. Defined.
  Next Obligation. f_equal; unfold ι; simpl; pi. Defined.
  Next Obligation. f_equal; unfold ι; simpl; pi. Defined.
  Next Obligation. admit. Defined. 
  Next Obligation. admit. Defined.

End Test.

  Notation " t '=_{' p '}'  u " := (eq_type p t u) (at level 90).

(* Goal True. *)
(*  nat_force (forall X : Set, X) at p as foo. *)
