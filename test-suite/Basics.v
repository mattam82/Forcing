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

  Notation subp := (@subp nat nat_condition).
  Notation sheaf := (@sheaf nat nat_condition).
  Notation sheafC := (@sheafC nat nat_condition).

  Obligation Tactic := idtac. (* program_simpl; auto with forcing. *)

    Time Force foo at p := (forall (f : nat -> Prop) (x : nat), f x).

Next Obligation. 
  intros. destruct q1, r1, s1; simpl in *; eauto with forcing. Admitted.
Next Obligation. 
  intros. simpl.  reflexivity.  Defined. 
Next Obligation. 
  intros. simpl.  reflexivity.  Defined. 
destruct q1, r1, s1; simpl in *; eauto with forcing. Admitted.



Next Obligation. 
  intros. auto with forcing. destruct r, r4, q6, q. simpl in *. eauto with arith.
  unfold ι. clear_subset_proofs. 
  specialize (H r4 s3 arg2).s
  unfold foo_obligation_2, eq_type in H; simpl in *. 
  unfold Init.subp in *; destruct_exists. simpl in *.
  unfold foo_obligation_1 in H. simpl in H. revert H; clear_subset_proofs.
  intros. rewrite <- H.
  simpl. unfold ι; simpl; clear_subset_proofs. reflexivity.
Defined.

Next Obligation. 
  unfold foo_obligation_2, eq_type in *; simpl in *.
  clear_subset_proofs. 
  rewrite (H  {Σ` r1, eqH}). clear_subset_proofs. reflexivity.
Defined.

Obligation Tactic := idtac.
Next Obligation. 
  intros. simpl proj1_sig.
  unfold foo_obligation_11, eq_type in arg. simpl in arg.
  destruct arg. clear_subset_proofs. specialize (e r4 s3 arg2).
  revert e; clear_subset_proofs. intros.
  rewrite <- e. simpl.  
  unfold ι. clear_subset_proofs. simpl. reflexivity.
Defined.

Next Obligation. 
  intros. clear. destruct r, s, s3; simpl in *; eauto with arith forcing.
Defined. 


Next Obligation. 
  intros; clear. destruct r, s; simpl in *; eauto with arith forcing. Defined.
Next Obligation. 
  intros; clear. destruct s1, s; simpl in *; eauto with arith forcing. Defined.
Next Obligation. 
  intros; clear. 
  unfold foo_obligation_11, eq_type in *; simpl in *.
  destruct arg. simpl. clear_subset_proofs. specialize (e {Σ` r1, eqH} s1 arg1).
  simpl in e. destruct r1; clear_subset_proofs. simpl in *. revert e. clear_subset_proofs.
  intros. rewrite <- e. pi.
Defined.

Next Obligation. 
  intros; clear. simpl. 
  unfold foo_obligation_14 at 2. destruct r. simpl. destruct arg. simpl. clear_subset_proofs.

Axiom prod_extensionality : forall A (B B' : A -> Type), (∀ x : A, B x = B' x) -> (∀ x : A, B x) = (∀ x : A, B' x).

  do 2 (apply prod_extensionality; intros). clear_subset_proofs. pi. Defined.
Next Obligation. 
  intros; clear. destruct s, r7; simpl in *; eauto with arith forcing.
Defined.

Print foo.
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
