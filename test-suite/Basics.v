Require Import Forcing.
Require Import RelationClasses.

Definition proj_sub {p : nat} : subp p -> nat :=
  fun x => proj1_sig x.

Coercion ι_refl : subp >-> subp.

Hint Extern 0 (_ = _) => apply ι_ι_refl : forcing.
Hint Extern 0 (_ <= _) => apply reflexivity : forcing. 

Notation " '{Σ' x , y } " := (exist _ x y).
Notation " '(Σ' x , y ) " := (existT _ x y).

Section Test.

  Variable p : nat.

  Hint Extern 1 (` ?x <= _) => apply (proj2_sig (ι x)) : forcing.

  Obligation Tactic := program_simpl; eauto with forcing.

  Force identity at p := (forall X : Set, X -> X).

  Lemma subp_surj : forall (p : nat) (q : subp p) (r : subp (` q)), r = (ι (p:=`q) r).
  Proof. intros. unfold ι. destruct r; simpl. pi. Defined.

  Next Obligation. f_equal. unfold ι; simpl; pi. Defined.
  Next Obligation. f_equal. unfold ι; simpl; pi. Defined.
  Next Obligation.
    specialize (f4 r4 X). destruct f4.
    red in arg2. destruct X. simpl in *.
    specialize (e s11 s10 arg2).
    revert e.
    on_call identity_obligation_2 ltac:(fun c => set(eq:=c)).
    simpl in eq.  unfold ι in eq. simpl in eq. 
    destruct s10, s11; simpl in *. revert eq.
    unfold eq_type, sheafC_obligation_1.
    autounfold with identity. unfold ι. simpl. 
    rewrite !eq_trans_eq_refl_l, !eq_rect_f_equal. 
    intros. clear e.

    unfold eq_type.
    rewrite !eq_rect_f_equal. 
    u
    abstract_eq_proofs.

clear e. simpl in *. 
    destruct s. red in x1. destruct a.
    red in H1, H2. 
    pose (H1 (ι s10)).
    rewrite <- !subp_surj. 

clearbody a. rewrite <- subp_surj in arg2. specialize (a arg2). specialize (H1 _ a).
    
    

    assert(x0 s11 = x0 (ι (p:=` r4) s11)). f_equal. unfold ι.
    simpl. destruct s11; pi.


    unfold ι in f5. destruct s11. simpl in *.
    revert f5 arg2.
    assert(transitivity (R:=le) (x:=x2) (y:=x2) (z:=` r4) (reflexivity x2) l = l). apply le_pi.
    destruct H3. intros. unfold ι in arg2. simpl in *.
    clear f5.

    f_equal. 
    pose (H1 _ (





  Force empty at p := (forall X : Set, X).

  Next Obligation. apply (proj2_sig (ι s)). Defined.
  Next Obligation. f_equal. 
    unfold ι, ι_refl. simpl. pi. Defined.

  Next Obligation. apply (proj2_sig (ι s)). Defined.
  Next Obligation. f_equal. 
    unfold ι, ι_refl. simpl. pi. Defined.

  Next Obligation. apply (proj2_sig (ι s)). Defined.

  Program Definition foo := (projT1 empty p).

  Eval hnf in foo.
    
apply (proj2_sig (ι s)). Defined.


Goal forall p : nat, True.  intros. 
(*   nat_force (forall X : Set, X) at p as foo. *)
Unset Printing Existential Instances.

Notation " t '=_{' p '}'  u " := (eq_type p t u) (at level 90).
Typeclasses eauto := debug 10.

  nat_force (forall X : Set, X) at p as foo.

  unfold proj1_sig in foo.

  
  Show Existentials.

Program Definition foo (p : nat) :=
(λ q : subp p,
      {f : ∀ (r : subp (P:=nat) (`q)) (X : sheaf (P:=nat) r), projT1 (sheafC (`r) r r X) r |
      ∀ (r : subp (P:=nat) q) (s : subp (P:=nat) r) (X : sheaf (P:=nat) r),
      f (ι s) (sheafC (`r) r s X) =_{ _ (* [p, q, f, r, s, X] *)}
      projT2 (sheafC (`r) r r X) r s (f r X)}).

  (λ q : subp (P:=nat) p,
    {f
      : ∀ (r : @subp nat nat_condition (`q))
      (X : sheaf (P:=nat) (`r)),
      sheaf_f (P:=nat) (sheafC (P:=nat) (`r) r r X) r
      | 
      ∀ (r : subp (P:=nat) (`q)) (s : subp (P:=nat) (`r))
      (X : sheaf (P:=nat) (`r)),
      let pr := proj1_sig (P:=fun x => le x (`q)) r in
      let sheaf := sheafC (P:=nat) pr r in
      let sheaf2 := sheafC (P:=nat) (`r) r r X in
        let fι := f (ι s) in
        let left := fι (sheaf s X) in
        let right := Θ sheaf2 r s (f r X) in
          left =_{ _ } right
            }).

Next Obligation.
  f_equal. 
  unfold ι, ι_refl. simpl. pi. 
Defined.
