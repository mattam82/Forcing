Require Import Forcing.
Require Import RelationClasses.

Notation " '{Σ' x , y } " := (exist x y).
Notation " '(Σ' x , y ) " := (existT x y).

Section Test.

  Import NatForcing.
  Import NatCondition.
   Open Scope forcing_scope.

Lemma subp_proof2 p (q : subp p) : ` q <= p. apply subp_proof. Defined.
Hint Resolve subp_proof2 : forcing.

Ltac forcing_le :=
  match goal with
    |- ` ?x <= ?y => 
      match type of x with
        subp ?r => transitivity r
      end
    | |- subp_proj ?x <= ?y => 
      match type of x with
        subp ?r => transitivity r
      end
  end.

Hint Extern 2 (_ <= _) => forcing_le : forcing.

  Obligation Tactic := program_simpl; auto with forcing.
Set Printing Existential Instances.
Print HintDb forcing.
Time Force foo := (forall (f : nat -> Prop) (x : nat), f x).

Next Obligation. 
  intros. destruct r. simpl in *.
  unfold ι. clear_subset_proofs. 
  specialize (H r4 s3 arg2).
  unfold foo_obligation_2, eq_type in H; simpl in *. 
  unfold subp in *; destruct_exists. simpl in *.
  unfold foo_obligation_1 in H. simpl in H. revert H; clear_subset_proofs.
  intros. rewrite <- H.
  simpl. unfold ι; simpl; clear_subset_proofs. reflexivity.
Defined.

Next Obligation. 
  unfold foo_obligation_2, eq_type in *; simpl in *. clear f.
  unfold subp_proj in *.
  clear_subset_proofs. unfold foo_obligation_1 in H. 
  generalize (H (@exist _ (fun r' => r' <= ` r) (` r1) eqH0) s1 arg1). 
  simpl in *. unfold subp_proj in *. clear_subset_proofs. intros. rewrite <- H0. reflexivity.
Defined.

Obligation Tactic := idtac.
Next Obligation. 
  intros. simpl proj1_sig.
  unfold foo_obligation_11, eq_type in arg. simpl in arg.
  unfold subp_proj in *.
  destruct arg. clear_subset_proofs. specialize (e r4 s3 arg2).
  revert e; clear_subset_proofs. simpl. intros.
  rewrite <- e. simpl. 
  unfold ι. unfold subp_proj in *. clear_subset_proofs. simpl. reflexivity.
Defined.

Next Obligation. 
  intros. clear. eauto with forcing. 
Defined. 

Next Obligation. 
  intros; clear. eauto with forcing. Defined.
Next Obligation. 
  intros; clear. eauto with arith forcing. Defined.
Next Obligation. 
  intros; clear. 
  unfold foo_obligation_11, eq_type in *; simpl in *.
  destruct arg. simpl. unfold subp_proj in *. clear_subset_proofs. 
  specialize (e {Σ` r1, eqH} s1 arg1).
  simpl in e. destruct r1; clear_subset_proofs. simpl in *. revert e. clear_subset_proofs.
  intros. rewrite <- e. pi.
Defined.

Next Obligation. 
  intros; clear. simpl. 
  unfold foo_obligation_14 at 2. destruct r. simpl. destruct arg. simpl. clear_subset_proofs.

Axiom prod_extensionality : forall A (B B' : A -> Type), (∀ x : A, B x = B' x) -> (∀ x : A, B x) = (∀ x : A, B' x).

  do 2 (apply prod_extensionality; intros). clear_subset_proofs. pi. Defined.
Next Obligation. intros.
  clear. destruct s, r7; simpl in *; eauto with arith forcing.
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
