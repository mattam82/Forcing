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

Program Definition later_sheaf_f {p : nat} (q : subp p) (T : sheaf q) : subp q -> Type :=
  fun r =>
    match r with
      | 0 => unit
      | S r' => sheaf_f T r'
    end.
Next Obligation of later_sheaf_f. unfold le. destruct r. simpl in *. subst x; auto with arith. Qed.

Program Definition subppred {q} (r : subp q) : subp q := pred r.
Next Obligation. intros. destruct r. simpl in *. unfold le in *. destruct x; eauto with arith. Defined.

Program Definition later_transp {p} (q : subp p) (T : sheaf q) : transport (later_sheaf_f q T) :=
  λ (r : subp q) (t : subp r) (M : later_sheaf_f q T r),
  let (tn, tprf) as t return later_sheaf_f q T (iota t) := t in
    match tn return forall prf : tn <= r, later_sheaf_f q T (iota (exist tn prf)) with 
      | 0 => fun prf => tt
      | S t' => fun prf => Θ T (subppred r) t' _
    end tprf.
  
Next Obligation. intros. destruct r, t. destruct x; simpl in *; unfold le in *; eauto with arith. Defined.

Next Obligation.
  destruct r as [[|r'] Hr]; simpl in *; unfold le in *. 
  elimtype False. depelim prf.

  unfold subppred; simpl.
  apply M.
Defined.

Program Definition embed (p : P) : subp p := p.

Forcing Operator later : (Type -> Type).

Notation " '{Σ'  x } " := (exist x _).

Lemma sigma_eq {A} {P : A -> Prop} (x y : A) (p : P x) (q : P y) : x = y -> {Σx, p} = {Σ y, q}. 
Proof. intros ->. reflexivity. Qed.

Next Obligation.
  red. intros.
  assert(forall p (q : subp p) (T : sheaf q), refl (later_transp q T) /\ trans (later_transp q T)). 
  intros.
  split; red; intros.
  destruct T as [s [trans prf]]. 
  destruct prf. red in r.
  revert x; case_eq q0.
  intros.
  unfold eq_rect.
  destruct x.
  simpl. destruct x0. reflexivity.
  simpl.
  unfold Θ.
  simpl in *. unfold later_sheaf_f in x0.
  simpl in x0. assert(x <= ` q) by (unfold le in *; auto with arith).
  pose proof (r ({Σx, H0})). 
  unfold eq_rect in H1.
  simpl. unfold subppred.
  simpl. apply H1.

  unfold compose.
  destruct T as [sh [trans [re tr]]]. 
  revert r s x; case_eq q0. intros.

  destruct s as [[|s'] prf].
  now simpl in *.
  
  destruct r as [[|r'] prfr].
  now simpl in *.

  destruct x.
  inversion prfr.
  simpl in * |-.
  red in tr.
  simpl in *.
  unfold compose in tr. unfold subppred.
  simpl. 
  assert(x <=  ` q) by (unfold le in *; auto with arith; admit).
  pose (x':={Σ x, H0}:subp q).
  pose proof (tr x').
  unfold Θ. simpl.
  assert(r' <= x) by (unfold le in *; auto with arith; admit).
  pose (rs':={Σ r', H2}:subp x').
  specialize (H1 rs'). assert (s' <= r') by admit.
  specialize (H1 ({Σ s', H3})).
  unfold later_sheaf_f in x0.
  simpl in x0. specialize (H1 x0).
  apply H1.

  refine (exist (λ q : subp p, λ T : sheaf q,
    existT (later_sheaf_f q T) (exist (later_transp q T) (H p q T))) _).
  intros.
  unfold sheafC. simpl. 
  destruct arg as [sh [transp [rt tt]]].
  simpl. apply f_equal. apply sigma_eq.
  unfold Θ. simpl.
  extensionality s0.
  extensionality t.
  extensionality x.
  destruct t. 
  simpl.
  destruct x0. reflexivity.
  apply f_equal.
  destruct s0.
  simpl. destruct x1; reflexivity. 
Defined.

Implicit Arguments forcing_traduction [[A] [ForcingOp]].

(* Forcing Operator ident : (forall T, T -> T). *)

(* Notation " '{Σ' x } " := (exist x _). *)
(* Next Obligation. *)
(*   red. intros. *)
(*   simpl.  *)
(*   assert(forall (r : subp p) (arg : sheaf r), {f1 : ∀ r1 : subp r, sheaf_f arg r1 → sheaf_f arg r1 | *)
(*      ∀ (r1 : subp r) (s1 : subp r1) (arg1 : sheaf_f arg r1), *)
(*      Θ arg (r1) s1 (f1 r1 arg1) = *)
(*      f1 {Σ` s1} (Θ arg r1 s1 arg1)}). *)
(*   intros. refine (exist (λ r1 x, x) _). *)
(*   reflexivity. unfold ι. simpl. *)
(*   refine (exist X _). *)
(*   simpl. *)
(*   intros. *)
(*   destruct s. *)
(*   simpl. *)
(*   reflexivity. *)

Notation " '{Σ' x } " := (exist x _).

Definition Pred (p : nat) := { x : nat | x < p }.

Program Definition Pred_to_sub (p : nat) (q : Pred p) : subp p := q.
Next Obligation of Pred_to_sub.  
  destruct q. simpl. red; auto with arith.
Defined.

Program Definition succ_of_Pred (p : nat) (q : Pred p) : subp p := S q.
Next Obligation of succ_of_Pred.  
  destruct q. simpl. auto with arith.
Defined.

Program Definition subp0 (p : nat) : subp p := 0.
Next Obligation of subp0.
  intros; auto with arith.
  red. auto with arith.
Defined.

(* Fixpoint subp_rect {q : nat} (P : subp q -> Type)  *)
(*                    (p0 : P subp0) (pS : forall r : subp q, P r -> P (Pred_to_sub q r)) *)
(*                    (r : subp q) : P r := *)
(*   match (r : subp q) return P r with *)
(*     | exist 0 prf => p0 *)
(*     | exist (S n) prf => pS n (subp_rect P p0 pS n) *)
(*   end. *)
Require Import Wf.

Lemma le_decr : forall n m, S n <= m -> n <= m.
Proof. intros. red in H |- *. inversion H. auto with arith.
  auto with arith.
Defined.

Fixpoint subp_rect_aux {q : nat} (P : subp q -> Type) 
                   (p0 : P (subp0 q)) (pS : forall r : Pred q, P (Pred_to_sub q r) -> P (succ_of_Pred q r))
                   (r : nat) (prf : r <= q) : P (exist r prf) :=
  match (exist r prf) as r' return P r' with
    | exist 0 prf => p0
    | exist (S n) prf => pS (exist n prf) (subp_rect_aux P p0 pS n (le_decr _ _ prf))
  end.

Definition subp_rect {q : nat} (P : subp q -> Type) 
                (p0 : P (subp0 q)) (pS : forall r : Pred q, P (Pred_to_sub q r) -> P (succ_of_Pred q r))
                (r : subp q) : P r :=
  let (r, rprf) as r' return P r' := r in
    subp_rect_aux P p0 pS r rprf.

Definition 
  innerfn :=
  fun p =>
    (fun (r : subp p) (arg : sheaf r) =>
       (fun (r1 : subp r) 
            (f2 : {f2
    : ∀ r2 : subp r1,
      later_sheaf_f (iota r2) (sheafC r (iota r) (iota r2) arg) (iota r2)
      → projT1 (sheafC r (iota r) (iota r2) arg) (iota r2) |
    ∀ (r2 : subp r1) (s2 : subp r2)
    (arg2 : later_sheaf_f (iota r2) (sheafC r (iota r) (iota r2) arg) (iota r2)),
    (` (projT2 (sheafC r (iota r) (iota r2) arg))) 
      (iota r2) (iota s2) (f2 r2 arg2) =
    f2 (iota s2)
      (later_transp (iota r2) (sheafC r (iota r) (iota r2) arg) 
         (iota r2) (iota s2) arg2)}) =>
                subp_rect (fun r : subp r1 => sheaf_f arg (iota r))
                          (` f2 (subp0 _) tt) 
                          (fun (r' : Pred (`r1)) a => ` f2 (succ_of_Pred _ r') a)
                          (iota r1))).
            
Obligation Tactic := idtac.

Forcing Operator fixp : (forall T : Type, (later T -> T) -> T).

Obligation Tactic := idtac.
Next Obligation.
  intros.
  clear f1 arg1. destruct s2, s1, r1; simpl in *; unfold le in *; auto with arith.
  now transitivity x0.
Qed.

Next Obligation. Opaque later_transp.
  simpl; intros. 
  destruct arg1 as [f2 Hf2].
  simpl in *.
  apply (Hf2 (iota r2) s2 arg2).
Qed.

Next Obligation.
  simpl; intros.
  clear f; destruct s, s1, r.
  simpl in *; eauto with arith. now transitivity x.
Qed.




Next Obligation.
  simpl; intros.
  red.

Program Definition secondfn :=
          (fun p (r : subp p) (arg : sheaf r) =>
             (exist (innerfn p r arg) _ : 
              {f1
     : ∀ r1 : subp r,
       {f2
       : ∀ r2 : subp r1,
         later_sheaf_f (iota_refl r2) (sheafC r (iota r) (iota r2) arg)
           (iota r2) → projT1 (sheafC r (iota r) (iota r2) arg) (iota r2) |
       ∀ (r2 : subp r1) (s2 : ssubp r2)
       (arg2 : later_sheaf_f (iota_refl r2) (sheafC r (iota r) (iota r2) arg)
                 (iota r2)),
       (` (projT2 (sheafC r (iota r) (iota r2) arg))) 
         (iota r2) (iota s2) (f2 r2 arg2) =
       f2 (iota s2)
         (later_transp (iota_refl r2) (sheafC r (iota r) (iota r2) arg)
            (iota r2) (iota s2) arg2)}
       → projT1 (sheafC r (iota r) (iota r1) arg) {Σ ` r1} |
     ∀ (r1 : subp r) (s1 : ssubp r1)
     (arg1 : {f2
             : ∀ r2 : subp r1,
               later_sheaf_f (iota_refl r2) (sheafC r (iota r) (iota r2) arg)
                 (iota r2) → projT1 (sheafC r (iota r) (iota r2) arg) (iota r2)
             |
             ∀ (r2 : subp r1) (s2 : ssubp r2)
             (arg2 : later_sheaf_f (iota_refl r2)
                       (sheafC r (iota r) (iota r2) arg) 
                       (iota r2)),
             (` (projT2 (sheafC r (iota r) (iota r2) arg))) 
               (iota r2) (iota s2) (f2 r2 arg2) =
             f2 (iota s2)
               (later_transp (iota_refl r2) (sheafC r (iota r) (iota r2) arg)
                  (iota r2) (iota s2) arg2)}),
     (` (projT2 (sheafC r (iota r) (iota r1) arg))) 
       (iota r1) (iota s1) (f1 r1 arg1) =
     f1 (iota s1) {Σ λ s2 : subp (iota s1), (` arg1) {Σ ` s2}}})).

Next Obligation of secondfn.
  red.
  intros.
  clear f1 arg1. unfold iota in *.
  simpl in s2.
  destruct s2, s1, r1; simpl in *.
  now transitivity x0.
Qed.


Next Obligation of secondfn.
  intros.
  simpl. simpl in *.
  destruct arg1.
  simpl. pose proof (e (iota r2)).
  apply H.
Qed.


Next Obligation of secondfn.
  simpl; intros.
  destruct arg1.
  destruct r1.
  pose proof (e (iota {Σ x0, l})).
  simpl in H. unfold ssubp in H.
  destruct x0.
  simpl in *.
  unfold innerfn.
  unfold subp_rect.
  simpl. unfold later_sheaf_f in H. 
  simpl in H. rewrite H.
  destruct s1.
  simpl in l0.
  inversion l0.
  subst x0.
  simpl.
  Transparent later_transp.
  simpl. reflexivity.

  destruct s1.
  unfold innerfn; simpl.
  clear H. 
  pose proof (e (iota_refl (S x0))).
  unfold ssubp in H.
  simpl in H.
  specialize (H {Σ x1, l0}).
  rewrite H.
  clear H.
  destruct x1.
  simpl.
  reflexivity.


  simpl.
  unfold Θ.
  simpl.
  

  unfold Θ.
  simpl.
  apply f_equal.
  
  

Qed.


Program Definition fix_trans : fixp_trans :=
          fun p =>
          (fun (r : subp p) (arg : sheaf r) =>
             (fun (r1 : subp r) f2  => 
                subp_rect (q:=r1) (fun r => sheaf_f arg r)
                          (f2 (subp0 _) tt) 
                          (fun r' a => f2 (succ_of_Pred (` r1) r') a)
                          r1 _)).
          


Next Obligation.
  red.
  simpl; intros.
  refine (exist 
            (fun (r : subp p) (arg : sheaf r) =>
               exist (fun (r1 : subp r) f2  => 
                        subp_rect (q:=` r1) (fun r => sheaf_f arg r1)
                                  (f2 subp0 tt) 
                                  (fun r' a => f2 (succ_of_Pred (` r1) r') a))
                             _) _).
                                


  clear f.
  destruct s1, s, r.
  simpl in *; unfold le in *; eauto with arith.
Qed.


Time Force foo := (forall X : Set, X).



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
