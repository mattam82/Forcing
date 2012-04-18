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

Notation " '{Σ'  x } " := (exist x _).

Lemma sigma_eq {A} {P : A -> Prop} (x y : A) (p : P x) (q : P y) : x = y -> {Σx, p} = {Σ y, q}. 
Proof. intros ->. reflexivity. Qed.

Forcing Operator later : (Type -> Type).

Lemma later_transp_transport p (q : subp p) (T : sheaf q) : trans_prop (later_transp q T).
Proof. red; intros.
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
Qed.

Program Definition later_trans_sheaf {p : nat} (q : subp p) (T : sheaf q) : sheaf q :=
          existT (later_sheaf_f q T) (exist (later_transp q T) (later_transp_transport p q T)).

Program Definition later_trans_impl : later_trans :=
          fun p : nat => exist later_trans_sheaf _.

Next Obligation of later_trans_impl.
  red. intros. simpl.
  unfold sheafC. simpl. 
  destruct arg as [sh [transp [rt tt]]].
  simpl. unfold later_trans_sheaf. apply f_equal. apply sigma_eq.
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
Qed.

Next Obligation.
  red.
  intros.
  exact (later_trans_impl p).
Defined.

Implicit Arguments forcing_traduction [[A] [ForcingOp]].

Notation " '{Σ' x } " := (exist x _).
Set Printing All.
Set Typeclasses Debug.

Time Forcing Operator next : (forall T : Set, T -> later T).

Notation ι r := (iota r).
  
Definition innernext_fnty {p} (r : subp p) (arg : sheaf r) :=
  ∀ r1 : subp r,
    sheaf_f arg r1
    → later_sheaf_f (iota_refl r1) (sheafC r (ι r) r1 arg) (ι r1).
 
Definition innernext_fncommpi {p} (r : subp p) (arg : sheaf r) (f1 : innernext_fnty r arg) :=
  ∀ (r1 : subp r) (s1 : subp r1) (arg1 : sheaf_f arg r1),
     later_transp (iota_refl r1) (sheafC r (ι r) r1 arg) (ι r1) s1 (f1 r1 arg1) =
                  f1 (ι s1) (Θ arg r1 s1 arg1).

Definition innernext_ty {p} (r : subp p) (arg : sheaf r) := sig (innernext_fncommpi r arg).

Program Definition innernextfn {p} (r : subp p) (arg : sheaf r) : innernext_fnty r arg :=
 (fun (r1 : subp r) =>
    let (r1t, r1prf) as r1 return sheaf_f arg r1 -> later_sheaf_f (iota_refl (`r1))
                                                                      (sheafC r (iota_refl r) r1 arg) (iota_refl r1) 
                                  := r1 in 
    (match r1t return forall H : r1t <= r, sheaf_f arg {Σ r1t, H} -> later_sheaf_f (iota_refl r1t)
                                                                      (sheafC r (iota_refl r) {Σ r1t, H} arg) (iota_refl r1t)  with
      | 0 => fun H sh => tt
      | S n => fun H sh => Θ arg {Σ S n, H} n sh
    end r1prf)).

Program Definition innernext {p} (r : subp p) (arg : sheaf r) : innernext_ty r arg := innernextfn r arg.

Hint Extern 4 => progress (unfold le in *) : forcing.

Next Obligation of innernext.  
Proof. Transparent later_transp. 
  red; intros. 
  destruct s1 as [[|s1'] Hs1]; simpl.
  reflexivity.
  destruct arg as [sh [tr [trr trt]]].
  simpl in *.
  red in trt.
  repeat unfold Θ. simpl.
  repeat unfold Θ. simpl.
  unfold iota in *; simpl.
  destruct r1 as [[|r1'] Hr1]; simpl in *.
  inversion Hs1. unfold compose in trt.

  assert(s1' <= r1') by auto with forcing arith.
  assert(r1' <= ` r) by auto with forcing arith.
  assert(r1' <= S r1') by auto with forcing arith.
  pose proof (trt {Σ S r1', Hr1} {Σ r1', H1} {Σ s1', H}).
  simpl in H2.
  rewrite H2.
  assert(s1' <= S s1') by auto with forcing arith.
  pose proof (trt {Σ S r1', Hr1} {Σ S s1', Hs1} {Σ s1', H3}).
  simpl in H4.
  rewrite H4.
  reflexivity.
Qed.
Unset Printing All.

(* Needs eta *)

Check (fun p (r : subp p) (q : subp r) => 
         eq_refl : (q : P) = (iota q : subp p)).

Next Obligation. 
Proof.
  red. Opaque later_transp.
  simpl. intros.
  refine (exist (@innernext p) _). 
  intros. 
  apply (functional_extensionality_dep). 
  intros. destruct x as [[|x'] Hx]. simpl.
  reflexivity.
  simpl.
  reflexivity.
Qed.

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

Forcing Operator fixp : (forall T : Type, (later T -> T) -> T).

Obligation Tactic := idtac.
Next Obligation.
  intros. 
  Opaque later_transp.
  destruct arg1 as [f2 Hf2].
  simpl in *.
  apply (Hf2 (iota r2) s2 arg2).
Qed.

Next Obligation.
  simpl; intros.
  clear. destruct s, s1, r.
  simpl in *; eauto with arith. now transitivity x.
Qed.

Global Program Instance iota_iota p (q : subp p) (r : P) {I : Iota p q r} : Iota p q (iota (Iota:=I) q : P) | 1000 := { iota := iota q }.
Next Obligation of iota_iota. intros. rewrite iota_identity. reflexivity. Qed.

Program Definition secondinnerinnerfnty p (r : subp p) (arg : sheaf r) (r1 : subp r) :=
 ∀ r2 : subp r1,
               later_sheaf_f (iota_refl r2) (sheafC r (iota r) (iota r2) arg)
                             (iota r2) → projT1 (sheafC r (iota r) (iota r2) arg) (iota r2).

Program Definition secondinnerinnerfnprop p (r : subp p) (arg : sheaf r) (r1 : subp r) 
                                     (f2 : secondinnerinnerfnty p r arg r1) :=
           ∀ (r2 : subp r1) (s2 : ssubp r2)
             (arg2 : later_sheaf_f (iota_refl r2) (sheafC r (iota r) (iota r2) arg)
                                   (iota r2)),
             (` (projT2 (sheafC r (iota r) (iota r2) arg))) 
               (iota r2) (iota s2) (f2 r2 arg2) =
               f2 (iota s2)
               (later_transp (iota_refl r2) (sheafC r (iota r) (iota r2) arg)
                             (iota r2) (iota s2) arg2).

Program Definition secondinnerfnty p (r : subp p) (arg : sheaf r) (r1 : subp r) :=
          sig (secondinnerinnerfnprop p r arg r1).

Program Definition secondfnty p (r : subp p) (arg : sheaf r) (r1 : subp r) :=
          secondinnerfnty p r arg r1 → projT1 (sheafC r (iota r) (iota r1) arg) (iota r1).


Example lif1 {p} {q : subp p} (r : subp q) : subp p.
Proof. exact (iota r). Defined.

Program Lemma secondfnprop_trans p (r : subp p) (arg : sheaf r) :
          ∀ (r1 : subp r) (s1 : subp r1) (arg1 : secondinnerfnty p r arg r1),
            secondinnerinnerfnprop p r arg (lif1 s1) (λ s2 : subp s1, (` arg1) (lif1 s2)).
  intros.
  red in arg1.
  destruct arg1 as [f2 Hf2].
  red in Hf2. red. simpl.
  intros. specialize (Hf2 (iota r2)).
  simpl in Hf2.
  apply Hf2.
Qed.

Program Definition lift_secondinnerfn p (r : subp p) (arg : sheaf r) (r1 : subp r) (arg1 : secondinnerfnty p r arg r1) (s1 : subp r1) : secondinnerfnty p r arg (lif1 s1) :=
          exist _ (secondfnprop_trans p r arg r1 s1 arg1).

Program Definition secondfnprop p (r : subp p) (arg : sheaf r) (f1 : forall r1 : subp r, secondfnty p r arg r1) :=
          ∀ (r1 : subp r) (s1 : subp r1)
            (arg1 : secondinnerfnty p r arg r1),
            ((` (projT2 (sheafC r (iota r) (iota r1) arg))) 
               (iota r1) (iota s1) (f1 r1 arg1) =
               f1 (iota s1) (lift_secondinnerfn p r arg r1 arg1 s1)).

Definition innerfn p (r : subp p) (arg : sheaf r) (r1 : subp r) : secondfnty p r arg r1 :=
  fun (f2 : secondinnerfnty p r arg r1) =>
    subp_rect (fun r : subp r1 => sheaf_f arg (iota r))
                          (` f2 (subp0 _) tt) 
                          (fun (r' : Pred (`r1)) a => ` f2 (succ_of_Pred _ r') a)
                          (iota r1).

Program Definition secondfn :=
          (fun p (r : subp p) (arg : sheaf r) =>
             (exist (innerfn p r arg) _ : sig (secondfnprop p r arg))).

Program Definition lift_subp {p} (q : subp p) : subp (S p) := q.
Next Obligation of lift_subp.
  intros p [q Hq].  
  simpl; unfold le in *; auto with arith.
Qed.

Program Definition lift_Pred {p} (q : Pred p) : Pred (S p) := q.
Next Obligation of lift_Pred.
  intros p [q Hq].  
  simpl; unfold le in *; auto with arith.
 Qed.
 
Lemma lift_subp_rect_aux {q : nat} (P : subp (S q) -> Type) 
                         (p0 : P (subp0 (S q))) 
                         (pS : forall r : Pred (S q), P (Pred_to_sub (S q) r) -> P (succ_of_Pred (S q) r))
                         (r : nat) (prf : r <= (S q)) (prf' : r <= q) : 
  subp_rect_aux P p0 pS r prf = subp_rect_aux (fun r : subp q => P (lift_subp r))
                p0 (fun r prf => pS (lift_Pred r) prf) r prf'.
Proof. induction r; simpl; auto.
  apply f_equal. apply IHr.
Qed.
Program Definition subp_le {p} (q : subp p) r (prf : p <= r) : subp r := q.
Next Obligation of subp_le.
  intros p [q Hq] ? ?. simpl; unfold le in *; eauto with arith.
Qed.

Ltac forward H :=
  match type of H with
    | forall X : ?T, _ => let arg := fresh in
                            assert (arg:T);[|specialize (H arg)]
  end.


Next Obligation of secondfn.
  simpl; intros.
  intros [r1 Hr1]. 
  induction r1; simpl; intros.
  unfold innerfn; simpl.
  unfold Θ in *; simpl in *.
  red in arg1.

  (* 0 *)
  destruct s1 as [[|s1] Hs1].
  simpl. 
  pose (proj2_sig arg1 (subp0 0) (subp0 _)). apply e.
  inversion Hs1.

  (* S n *)
  Transparent later_transp.
  forward IHr1; auto with arith forcing.
  pose (proj2_sig arg1 (embed (S r1)) s1).
  simpl in e.
  unfold innerfn.
  simpl. rewrite e. clear e.
  destruct s1 as [[|s1] Hs1]; simpl; auto.
  apply f_equal.
  unfold innerfn in IHr1.
  simpl in *.

  simpl.
  assert(s1 <= r1) by auto with forcing arith.
  assert(r1 <= r1) by reflexivity.
  rewrite lift_subp_rect_aux with (prf':=H1).
  rewrite lift_subp_rect_aux with (prf':=reflexivity s1 : s1 <= s1).
  specialize (IHr1 {Σ s1, H0}).
  simpl in IHr1.
  repeat (unfold Θ in *; simpl in *).
  specialize (IHr1 (lift_secondinnerfn p r arg _ arg1 (lift_subp (embed r1)))).
  simpl in IHr1.
  apply IHr1.
Qed.

Next Obligation.
  red.
  intros p.
  change {f : forall r arg, sig (secondfnprop p r arg) |
             ∀ (r : subp p) (s : ssubp r) (arg : sheaf r),
               (λ s1 : subp (` s), (` (f r arg)) (iota s1)) =
                                                           ` (f (ι s) (sheafC r (ι r) s arg))}.
  exists (secondfn p).
  intros. reflexivity.
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
