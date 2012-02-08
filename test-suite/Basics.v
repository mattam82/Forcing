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

  Obligation Tactic := program_simpl; eauto 2 with forcing.
    Unset Printing All.
  Force app at p := (forall (f : nat -> Prop), Set).


Set Typeclasses Debug.
    Program Definition foo : subp p -> Type :=

     (λ q55 : subp p,
      {f15
      : ∀ (r40 : subp (` q55))
        (f : {f16 : ∀ r41 : subp (` r40), nat → sheaf (`r41) |
             ∀ (r41 : subp r40) (s26 : subp r41) (arg5 : nat),
             eq_type _ (f16 s26 arg5) (sheafC (`r41) r41 s26 (f16 r41 arg5))}),
        {f17
        : ∀ (r44 : subp r40) (x : nat),
          projT1 (f r44 x) r44 |
        ∀ (r44 : subp r40) (s28 : subp r44) (x : nat),
        eq_type _ (f17 s28 x)
          (projT2 (f r44 x) r44 s28 (f17 r44 x))} |
        
      ∀ (r40 : subp q55) (s25 : subp r40)
      (f : {f16 : ∀ r41 : subp r40, nat → sheaf r41 |
           ∀ (r41 : subp r40) (s26 : subp r41) (arg5 : nat),
           eq_type _ (f16 s26 arg5) (sheafC r41 r41 s26 (f16 r41 arg5))}),
      True }).

(*       eq_type _ (f15 (ι s25) f) *)
(*         (f15 r40 f)}). *)


Next Obligation.
  intros. 
  unfold foo_obligation_3. 
  specialize (H r12 s8 x).
  unfold foo_obligation_2 in H. unfold eq_type in H. simpl in H.
  destruct r8, r12, s8. simpl in *. unfold ι; simpl. 
  unfold foo_obligation_1 in H. simpl in H.
  rewrite H.
  unfold sheafC. simpl. unfold sheaf_f. f_equal. unfold ι. simpl. pi.
Defined.
  
  
  


      ∀ (r8 : subp q11) (s5 : subp r8)
      (f : {f4 : ∀ r9 : subp r8, nat → sheaf r9 |
           ∀ (r9 : subp r8) (s6 : subp r9) (arg1 : nat),
           eq_type _ (f4 s6 arg1) (sheafC r9 r9 s6 (f4 r9 arg1))}),
      eq_type _ (f3 s5 (λ s6 : subp s5, f s6)) (λ s8 : subp s5, f3 r8 f s8)}).





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
