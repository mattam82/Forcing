Require Import Forcing.
Require Import RelationClasses.

Import NatForcing.
Import NatCondition.
Open Scope forcing_scope.

Hint Extern 4 => progress (unfold le in *) : forcing.

Class Have (P : Prop) := have_proof : P.

Program Definition inject {q} (r : P) {prf : Have (r <= q)} : subp q := r.
Hint Extern 0 (Have ?P) => red; auto : typeclass_instances.

Require Import Program.

Program Definition subp0 (p : nat) : subp p := 0.
Program Definition subpS (p : nat) (q : nat) (prf: q <= p): subp (S p) := q.
Program Definition subp_embed {p : nat} (q : subp p) : subp (S p) := q.
Program Definition subp_succ {p : nat} (q : subp p) : subp (S p) := S q.
Next Obligation. red. destruct q as [q Hq]; red in Hq; simpl in *. forcing. Qed.

Lemma le_plus_1 {n m} (prf : n <= m) : S n <= S m.
Proof. forcing. Defined.

Definition case_subp (Q : forall p, subp p -> Type) 
                     (P0 : forall p, Q p (subp0 p))
                     (PS : forall p (q : subp p), Q (S p) (subp_succ q)) 
                     p (q : subp p) : Q p q.
  change q with {Σ proj1_sig q, proj2_sig q}.
  generalize (proj2_sig q).
  destruct (proj1_sig q) as [|q']; intro Hq; red in Hq.
  apply P0.
  destruct p. elimtype False; inversion Hq.
  assert (q' <= p) by forcing.
  apply (PS p (subp_intro q' H)).
Defined.                     

Ltac destruct_sigma q :=
  let q' := fresh q in let Hq := fresh in
  change q with {Σ proj1_sig q, proj2_sig q};
  generalize (proj2_sig q) ;
  destruct (proj1_sig q) as [|q']; intro Hq; red in Hq.

Definition case_subp2 (Q : forall p (q : subp p) (r : subp q), Type) 
                     (P0 : forall p (q : subp p), Q p q (subp0 (subp_proj q)))
                     (PS : forall p (q : subp p) (r : subp q), Q (S p) (subp_succ q) (subp_succ r)) 
                     p (q : subp p) (r : subp q) : Q p q r.
Proof. 
  destruct_sigma r.
  apply P0.

  destruct p. elimtype False. revert H. 
  destruct_sigma q. 
  intros Hq. inversion Hq. inversion H.

  revert H; destruct_sigma q. intros Hq.
  elimtype False; inversion Hq.
  simpl in *. intros. assert (q0 <= p) by forcing; assert(r0 <= q0) by forcing.
  apply (PS p (subp_intro q0 H1) (subp_intro r0 H2)).
Defined.                     

Definition match_sub_subp {p} (Q : subp p -> Type) (P : forall (q : subp p) (A : Q q) (r : subp q), Type)
                          (P0 : forall (q : subp p) (qq : Q q), P q qq (subp0 (subp_proj q)))
                          (PS : forall (q' : nat) (prf : S q' <= p) (qq : Q {Σ S q', prf}) (r' : subp q'), 
                                  P {Σ S q', prf} qq {Σ S (subp_proj r'), le_plus_1 (proj2_sig r')})
                          (q : subp p) (qq : Q q) (r : subp q) : P q qq r.
change r with {Σ ` r, proj2_sig r}.
generalize (proj2_sig r).
destruct (` r) as [|r']; intros Hr; red in Hr; simpl in *.
apply P0.  

revert qq r Hr.
change q with {Σ ` q, proj2_sig q}.
generalize (proj2_sig q).
destruct (` q) as [|q']; intros. red in p0; simpl in *.
elimtype False; inversion Hr. 
assert(r' <= q') by forcing.
pose (PS q' p0 qq {Σ r', H}). simpl in p1. apply p1.
Defined.

Lemma match_sub_subp_0 {p} (Q : subp p -> Type) (P : forall (q : subp p) (A : Q q) (r : subp q), Type)
                          (P0 : forall (q : subp p) (qq : Q q), P q qq (subp0 (subp_proj q)))
                          (PS : forall (q' : nat) (prf : S q' <= p) (qq : Q {Σ S q', prf}) (r' : subp q'),
                                  P {Σ S q', prf} qq {Σ S (subp_proj r'), le_plus_1 (proj2_sig r')})

                          (Pcall : forall (q : subp p) (qq : Q q) (r : subp q) (call : P q qq r), Type)
                          (P0Call : forall (q : subp p) (qq : Q q), Pcall q qq (subp0 (subp_proj q)) (P0 q qq))
                          (PSCall : forall (q' : nat) (prf : S q' <= p) (qq : Q {Σ S q', prf}) (r' : subp q'),
                                      Pcall {Σ S q', prf} qq {Σ S (subp_proj r'), le_plus_1 (proj2_sig r')} (PS q' prf qq r'))

                          (q : subp p) (qq : Q q) (r : subp q) : Pcall q qq r (match_sub_subp Q P P0 PS q qq r).
destruct q as [[|q] Hq];
destruct r as [[|r] Hr]; red in Hq, Hr; simpl in *.
apply P0Call.  elimtype False; inversion Hr.
apply P0Call.
assert(r <= q) by forcing.
pose (PSCall q Hq qq {Σ r, H}). simpl in p0. apply p0.
Qed.

Program Definition subppred {q} (r : subp q) : subp q := pred r.
Next Obligation. intros. destruct r. simpl in *. unfold le in *. destruct x; forcing. Defined.

(* Program Definition later_sheaf_f {p : nat} (q : subp p) (T : sheaf q) : subp q -> Type := *)
(*           fun r => *)
(*           case_subp (fun p sp => sheaf p -> Type) *)
(*                     (fun p _ => unit) *)
(*                     (fun p q T => sheaf_f T q) *)
(*                     q r T.  *)

(* Program Definition transp {p : P} (s : sheaf p) : transport (sheaf_f s) := *)
(*           projT2 s. *)

(* Definition later_transp {p} (q : subp p) (T : sheaf q) : transport (later_sheaf_f q T) := *)
(*           λ (r : subp q) (t : subp r) (M : later_sheaf_f q T r), *)
(*           case_subp2 (fun p (r : subp p) (t : subp r) => forall T : sheaf p, later_sheaf_f (embed p) T r ->  *)
(*                                                                              later_sheaf_f (embed p) T (iota t)) *)
(*                     (fun p r sh lsh => tt) *)
(*                     (fun p q r sh lsh => transp sh (subp_embed q) r lsh) *)
(*                     q r t T M.  *)


Program Definition later_sheaf_f {p : nat} (q : subp p) (T : sheaf q) : subp q -> Type :=
  fun r =>
    match r with
      | 0 => unit
      | S r' => sheaf_f T r'
    end.
Next Obligation of later_sheaf_f. unfold le. destruct r. simpl in *. subst x; forcing. Qed.

Program Definition later_transp {p} (q : subp p) (T : sheaf q) : transport (later_sheaf_f q T) :=
  λ (r : subp q) (t : subp r) (M : later_sheaf_f q T r),
  match ` t as tn return forall prf : tn <= r, later_sheaf_f q T (iota (exist tn prf)) with
    | 0 => fun prf => tt
    | S t' => fun prf => Θ T (subppred r) t' _
  end (proj2_sig t).
  
Next Obligation. intros. destruct r, t. destruct x; simpl in *; forcing. Defined.

Next Obligation.
  destruct r as [[|r'] Hr]; simpl in *; unfold le in *.
  elimtype False. depelim prf.

  unfold subppred; simpl.
  apply M.
Defined.

Notation " '{Σ'  x } " := (exist x _).

Forcing Operator later : (Type -> Type).

Lemma later_transp_transport p (q : subp p) (T : sheaf q) : trans_prop (later_transp q T).
Proof. red; intros.
  split; red; intros.
  destruct T as [s [trans prf]]. 
  destruct prf. red in r.
  revert x; case_eq q0.
  intros.
  subst q0.
  destruct x.
  simpl. destruct x0. reflexivity.
  simpl.
  unfold Θ.
  simpl in *. unfold later_sheaf_f in x0.
  simpl in x0. assert(x <= ` q) by (unfold le in *; auto with arith).
  pose proof (r {Σ x, H}).
  destruct q as [[|q] Hq]; simpl.
  now simpl in p0.
  unfold later_transp. simpl. apply H0. 

  unfold compose.
  destruct T as [sh [trans [re tr]]]. 
  revert r s x; case_eq q0. intros.

  subst.
  destruct s as [[|s'] prf].
  now simpl in *.
  
  destruct r as [[|r'] prfr].
  now simpl in *.

  destruct x as [|x].
  inversion prfr.

  red in tr.
  unfold compose in tr.
  abstract_subset_proofs.
  assert(x <= ` q) by forcing.
  assert(s' <= r') by forcing.
  assert(r' <= x) by forcing.
  pose (tr (inject x) (inject r') (inject s')). simpl in e.
  destruct q as [[|q'] Hq].
  now simpl in x0.
  apply (e x0).
Qed.

Program Definition later_trans_sheaf {p : nat} (q : subp p) (T : sheaf q) : sheaf q :=
          existT (later_sheaf_f q T) (exist (later_transp q T) (later_transp_transport p q T)).

Program Definition later_trans_impl : later_trans :=
          fun p : nat => exist later_trans_sheaf _.

Next Obligation of later_trans_impl.
  red; intros.
  unfold sheafC.
  destruct arg as [sh [transp [rt tt]]].
  simpl. unfold later_trans_sheaf. simpl. 
  unfold later_sheaf_f.
  unfold case_subp.
  simpl.
  apply f_equal. apply exist_eq.
  unfold Θ. simpl.
  extensionality s0.
  extensionality t.
  extensionality x.
  destruct t. 
  destruct x0. reflexivity.
  unfold later_transp. simpl.
  apply f_equal.
  destruct s0.
  simpl. destruct x1; reflexivity. 
Qed.

Next Obligation.
  red.
  intros.
  exact (later_trans_impl p).
Defined.

Notation " '{Σ' x } " := (exist x _). Obligations.

Time Forcing Operator switch : (later Type -> Type).


Program Definition weaken {p} (r : subp p) (r' : nat) (prf : ` r = S r') : subp p := r'.
Next Obligation of weaken. red. destruct r. simpl in *. subst. red in p0. forcing. Qed.

Definition cast_later_sheaf_f {p} (q : subp p) (sh : later_sheaf_f (embed q) (sheafC_sheaf q) (embed q))
                              (r : subp q) (r' : nat) (prf : ` r = S r') : sheaf_f (sheafC_sheaf q) (subppred (embed q)).
Proof.
  destruct r as [[|r] Hr]; simpl in *; subst.
  destruct q as [[|q] Hq]; unfold later_sheaf_f in sh; simpl in *.
  discriminate. exact sh.
  destruct q as [[|q] Hq]; unfold later_sheaf_f in sh; simpl in sh.
  red in Hr. elimtype False; inversion Hr.
  exact sh.
Defined.

Program Definition switch_sheaf_def {p : nat} (q : subp p)
                                    (sh : later_sheaf_f (embed q) (sheafC_sheaf q) (embed q))
                                    (r : subp q) : Type :=
          match ` r with
            | 0 => unit
            | S r' => sheaf_f (cast_later_sheaf_f q sh r r' _) r'
          end.
Next Obligation of switch_sheaf_def.
Proof.
  red. destruct r; simpl in *; subst.
  red in p0. unfold le in *. 
  destruct q; simpl in *; auto with arith.
  destruct x; simpl in *; auto with arith.
Defined.  

(* Program Definition switch_sheaf_def {p : nat} := *)
(*           match_sub_subp (fun r : subp p => later_sheaf_f (embed r) (sheafC_sheaf r) (embed r)) *)
(*                          (fun r lsh sh => Type) *)
(*                          (fun q shq => unit) *)
(*                          (fun q prf shq r' => sheaf_f shq r'). *)

Program Definition switch_def {p : nat} : {x | switch_transprop p (embed p) x} :=
          fun r sh => existT (switch_sheaf_def r sh) (λ s t sh', _).
            
Program Definition transp {p : P} (s : sheaf p) : transport (sheaf_f s) :=
          projT2 s.

Next Obligation of switch_def.
  destruct s as [[|s] Hs]; simpl in *.
  destruct t as [[|t] Ht]; simpl in *.
  exact tt.

  destruct r as [[|r] Hr]; simpl in *.
  unfold switch_sheaf_def. simpl.
  bang.
  red in Ht. elimtype False; inversion Ht.

  destruct t as [[|t] Ht]; simpl in *.
  exact tt.
  destruct r as [[|r] Hr]; simpl in *.
  unfold switch_sheaf_def, match_sub_subp in sh' |- *. simpl.
  bang.

  assert(s <= r) by forcing.
  assert(t <= s) by forcing.
  pose (transp sh {Σ s, H} {Σ t, H0}).
  apply (a sh').
Defined.

Next Obligation of switch_def.
  red; split; red; intros.
  destruct q as [[|q] Hq]. simpl in *.
  destruct x; auto.
  simpl in x.
  destruct r as [[|r] Hr]. simpl in *.
  bang.

  assert(q <= r) by forcing.
  pose (sheaf_refl sh {Σ q, H}). apply e.

  unfold compose.
  destruct s as [[|s] Hs], q as [[|q] Hq], r as [[|r] Hr]; simpl in *; auto.
  destruct r0 as [[|r0] Hr0]; simpl; auto.
  bang. bang.  
  destruct r0 as [[|r0] Hr0]; simpl; auto.
  bang.  

  abstract_subset_proofs.
  apply (sheaf_trans sh (inject q) (inject r0) (inject s)). 
Qed.
Notation " 'cast' p 'in' x " := (eq_rect _ _ x _ p) (at level 10).

Lemma equal_existT {A} {P : A -> Type} {p q : A} {x : P p} {y : P q} : p = q -> (forall H : p = q, cast H in x = y) ->
                                                                       existT p x = existT q y.
Proof. intros. subst. f_equal.  apply (H0 eq_refl). Qed.

Lemma equal_existT_ext {A B} {P : (A -> B) -> Type} {p q : A -> B} {x : P p} {y : P q} 
  : (forall x : A, p x = q x) -> (forall H : p = q, cast H in x = y) ->
    existT p x = existT q y.
Proof. intros.
  assert (p = q).
  now extensionality g.
  subst. f_equal.  apply (H0 eq_refl). 
Qed.

Lemma cast_exist {C} (c d : C) (prf : c = d) {A : C -> Type} {P : forall c : C, A c -> Prop} {p : A c} {q : A d} (prf1 : P c p) (prf2 : P d q) :
  cast prf in p = q ->
  @eq (sig (P d)) (eq_rect c (fun c => sig (P c)) (@exist (A c) (P c) p prf1) d prf) (@exist (A d) (P d) q prf2).
Proof. destruct prf. simpl.
  apply exist_eq.
Qed.

Lemma cast_lambda {C} (c d : C) (prf : c = d) {A : Type} {P : A -> C -> Type} 
                  (t1 : forall x : A, P x c) 
                  (t2 : forall x : A, P x d) :
  (forall x : A, cast prf in (t1 x) = t2 x) ->
  @eq (forall x : A, P x d) (eq_rect c (fun c => forall x : A, P x c) (λ x : A, t1 x) d prf) (λ x : A, t2 x).
Proof. destruct prf. simpl.
  intros. 
  extensionality xa.
  apply H.
Qed.

  Lemma eq_rect_unnecessary {A} (P : A -> Type) (a b : A) (prf : a = b) (x : P a) (prf2 : P a = P b) : 
    cast prf in x = eq_rect _ (fun P => P) x _ prf2.
  Proof.
    revert x prf2. destruct prf.

    intros.
    simpl. unfold eq_rect.
    reflexivity.
  Qed.

Next Obligation of switch_def.
  red. intros. unfold sheafC.
  unfold sheaf_f. unfold projT1.
  symmetry.
  refine (equal_existT_ext _ _).
  intros. simpl.
  unfold switch_sheaf_def, match_sub_subp.
  destruct x as [[|x] Hx]; simpl. 
  reflexivity.
  destruct s as [[|s] Hs]; simpl.
  bang.

  simpl in Hx.
  destruct r as [[|r] Hr]; simpl.
  now simpl in Hs.
  reflexivity.

  intros.
  simpl.
  apply cast_exist.
  refine (@cast_lambda _ _ _ H _ _ _ _ _).
  intros.
  refine (@cast_lambda _ _ _ H _ _ _ _ _).
  intros x0.
  destruct x as [[|x] Hx]; simpl.
  destruct x0 as [[|x0] Hx0]; simpl.
  unfold Θ. simpl. reflexivity.

  now simpl in Hx0.

  destruct x0 as [[|x0] Hx0]; simpl.
  unfold Θ. simpl. reflexivity.

  destruct s as [[|s] Hs]; simpl.
  bang.

  destruct r as [[|r] Hr]; simpl.
  now simpl in Hs.
  unfold Θ. simpl.
  unfold later_transp. simpl.
  unfold Θ. simpl.
  unfold subppred. simpl.
  unfold switch_sheaf_def. simpl.

  red in Hr, Hs, Hx, Hx0; simpl in *.
  assert(x0 <= x /\ x <= s /\ s <= r /\ r <= p) by forcing.
  assert(x <= r) by (transitivity s; forcing).
  assert(x0 <= r) by (transitivity x; forcing).

  pose proof (eq_rect_unnecessary (fun ty : subp (S s) -> Type => 
                               ty (inject (S x)) -> projT1 arg (inject x0)) _ _ H). 
  simpl in H3.
  unfold switch_sheaf_def in H3. simpl in H3.
  match goal with
      |- eq_rect _ _ ?x _ _ = _ => set (fn:=x)
  end.
  specialize (H3 fn eq_refl).
  simpl in H3.
  transitivity fn.
  assumption.
  subst fn.
  reflexivity.
Qed.   

Ltac forward H :=
  match type of H with
    | forall X : ?T, _ => let arg := fresh in
                            assert (arg:T);[|specialize (H arg)]
  end.

Next Obligation.
Proof.
  red.
  exact @switch_def.
Defined.

Time Forcing Operator next : (forall T : Type, T -> later T).

Next Obligation.
  intros. red; simpl; intros. 
  apply (H (one_trans _ _ _ r1)).
Qed.

Next Obligation.
  red; simpl; intros. split ; red; intros; reflexivity.
Qed.
  
Definition innernext_fnty {p} (r : subp p) (arg : sheaf r) :=
  ∀ r1 : subp r,
    sheaf_f arg r1
    → later_sheaf_f (embed r1) (sheafC r (ι r) r1 arg) (ι r1).
 
Definition innernext_fncommpi {p} (r : subp p) (arg : sheaf r) (f1 : innernext_fnty r arg) :=
  ∀ (r1 : subp r) (s1 : subp r1) (arg1 : sheaf_f arg r1),
     later_transp (embed r1) (sheafC r (ι r) r1 arg) (ι r1) s1 (f1 r1 arg1) =
                  f1 (ι s1) (Θ arg r1 s1 arg1).

Definition innernext_ty {p} (r : subp p) (arg : sheaf r) := sig (innernext_fncommpi r arg).


Coercion embed : P >-> subp.

Program Definition innernextfn {p} (r : subp p) (arg : sheaf r) : innernext_fnty r arg :=
 (fun (r1 : subp r) =>
    let (r1t, r1prf) as r1 return sheaf_f arg r1 -> later_sheaf_f (`r1)
                                                                      (sheafC r r r1 arg) (embed r1) 
                                  := r1 in 
    (match r1t return forall H : r1t <= r, sheaf_f arg {Σ r1t, H} -> later_sheaf_f (embed r1t)
                                                                      (sheafC r (embed r) {Σ r1t, H} arg) (embed r1t)  with
      | 0 => fun H sh => tt
      | S n => fun H sh => Θ arg {Σ S n, H} n sh
    end r1prf)).

Program Definition innernext {p} (r : subp p) (arg : sheaf r) : innernext_ty r arg := innernextfn r arg.

Next Obligation of innernext.  
Proof. Transparent later_transp. 
  red; intros. 
  destruct s1 as [[|s1'] Hs1]; simpl.
  reflexivity.
  destruct arg as [sh [tr [trr trt]]].
  simpl in *.
  red in trt.
  destruct r1 as [[|r1'] Hr1]; simpl in *.
  inversion Hs1. 

  repeat (unfold later_transp, Θ; simpl).
  unfold compose in trt.

  assert(s1' <= r1') by auto with forcing arith.
  assert(r1' <= ` r) by auto with forcing arith.
  assert(r1' <= S r1') by auto with forcing arith.
  pose proof (trt {Σ S r1', Hr1} {Σ r1', H1} {Σ s1', H}).
  simpl in H2.
  assert(s1' <= S s1') by auto with forcing arith.
  pose proof (trt {Σ S r1', Hr1} {Σ S s1', Hs1} {Σ s1', H3}).
  simpl in H4.
  now rewrite H4, H2.
Qed.

Transparent later_transp. 
Program Definition nextdef p : { x | next_transprop1 p (embed p) x } :=
            @innernext p.

Next Obligation of nextdef.
Proof.
  red; intros.
  pose proof (proj2_sig (innernext r arg)).
  red in H. apply exist_eq.
  extensionality s1.
  extensionality arg1.
  destruct s1 as [[|x'] Hx]; simpl; reflexivity.
Qed.

Next Obligation.
Proof. exact nextdef. Defined.

Forcing Operator fixp : (forall T : Type, (later T -> T) -> T).

(** Should be automatable: simple reindexings of commutation
  properties. *)

Next Obligation.
Proof.
  red in H; simpl in H.
  red; simpl; intros; apply (H (iota r2) s2 arg2).
Qed.

Next Obligation.
  red; split; red; intros; reflexivity.
Qed.

Next Obligation.
  red. simpl.
  intros.
  unfold fixp_transprop1 in H. 
  apply (H (iota r1) s1).
Qed.

Next Obligation.
  red; split; red; intros; reflexivity.
Qed.

Definition Pred (p : nat) := { x : nat | x < p }.

Program Definition Pred_to_sub (p : nat) (q : Pred p) : subp p := q.
Next Obligation of Pred_to_sub.  
  destruct q; forcing. 
Defined.

Program Definition succ_of_Pred (p : nat) (q : Pred p) : subp p := S q.
Next Obligation of succ_of_Pred.  
  destruct q; forcing. 
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

Global Program Instance iota_iota p (q : subp p) (r : P) {I : Iota p q r} : Iota p q (iota (Iota:=I) q : P) | 1000 := { iota := iota q }.
Next Obligation of iota_iota. intros. rewrite iota_identity. reflexivity. Qed.

Program Definition secondinnerinnerfnty p (r : subp p) (arg : sheaf r) (r1 : subp r) :=
 ∀ r2 : subp r1,
               later_sheaf_f (embed r2) (sheafC r (iota r) (iota r2) arg)
                             (iota r2) → projT1 (sheafC r (iota r) (iota r2) arg) (iota r2).

Program Definition secondinnerinnerfnprop p (r : subp p) (arg : sheaf r) (r1 : subp r) 
                                     (f2 : secondinnerinnerfnty p r arg r1) :=
           ∀ (r2 : subp r1) (s2 : ssubp r2)
             (arg2 : later_sheaf_f (embed r2) (sheafC r (iota r) (iota r2) arg)
                                   (iota r2)),
             (` (projT2 (sheafC r (iota r) (iota r2) arg))) 
               (iota r2) (iota s2) (f2 r2 arg2) =
               f2 (iota s2)
               (later_transp (embed r2) (sheafC r (iota r) (iota r2) arg)
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
Program Definition lift_Pred {p} (q : Pred p) : Pred (S p) := q.
Next Obligation of lift_Pred.
  destruct q as [q Hq]. forcing.
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

Lemma innerfn_prop p r arg : secondfnprop p r arg (innerfn p r arg).

  intros [r1 Hr1]. 
  induction r1; simpl; intros.

  (* 0 *)
  destruct s1 as [[|s1] Hs1]; simpl.
  apply (proj2_sig arg1 (subp0 0) (subp0 _)). 
  inversion Hs1.

  (* S n *)
  Transparent later_transp.
  forward IHr1; forcing.
  pose (proj2_sig arg1 (embed (S r1)) s1).
  simpl in e.
  unfold innerfn.
  simpl. rewrite e. clear e.
  destruct s1 as [[|s1] Hs1]; simpl; auto.
  apply f_equal.
  unfold innerfn in IHr1.
  simpl in *.

  simpl.
  assert(s1 <= r1) by forcing.
  assert(r1 <= r1) by forcing.
  rewrite lift_subp_rect_aux with (prf':=H1).
  rewrite lift_subp_rect_aux with (prf':=reflexivity s1 : s1 <= s1).
  specialize (IHr1 {Σ s1, H0}).
  simpl in IHr1.
  repeat (unfold Θ in *; simpl in *).
  specialize (IHr1 (lift_secondinnerfn p r arg _ arg1 (lift_subp (embed r1)))).
  simpl in IHr1.
  apply IHr1.
Qed.

Next Obligation of secondfn.
  apply innerfn_prop.
Qed.

Next Obligation.
  red.
  intros p.
  exists (secondfn p).
  red; intros. reflexivity.
Defined.
