Require Import Forcing.
Import NatForcing.
Import NatCondition.
Open Scope forcing_scope.

Require Import "fix". 
Require Import eqf_def.

Hint Extern 4 => progress (unfold le in *) : forcing.

Obligation Tactic := program_simpl; forcing.

Forcing
Lemma switch_next : (forall A : Type, eqf Type (switch (next _  A)) (later A)).
Next Obligation.
Proof.
  red. intros. red.
  destruct r as (r,Hr). intros; red. intros.
  unfold Θ. simpl.
  apply f_equal.
  refine (equal_existT_ext _ _).
  intros.
  unfold later_trans_sheaf. simpl.
  unfold later_sheaf_f, switch_sheaf_def. simpl.
  destruct x as [[|x] Hx]; simpl. reflexivity.
  destruct r. bang.
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
  destruct r. bang.

  match goal with
      |- context [ eq_rect _ _ ?fn _ _ ] => set(f:=fn)
  end.
  assert(S t <= S r) by (transitivity (S s); forcing).
  assert(S s <= S r) by (forcing).
  transitivity f.
  apply (eq_rect_unnecessary (fun ty : subp (S r) -> Type =>
                                ty (inject (S s)) -> ty (inject (S t))) _ _ H f eq_refl).
  subst f. reflexivity.
Qed.

Forcing
Lemma eqfix : (forall (G: later Type -> Type), eqf _ (fixp _ G) (G (next _ (fixp _ G)))).

Next Obligation.
  red; simpl; intros; red in H.
  apply (H (iota r1) s1 arg1).
Qed.

Next Obligation.
  red; split; red; intros; reflexivity.
Qed.

Next Obligation.
  red; simpl; intro p.
  red; simpl; intros [q Hq] f.
  red; simpl.
  intro r; apply f_equal; simpl. clear r.
  induction q.
  reflexivity.
  
  unfold innerfn at 1. simpl.
  apply f_equal; simpl.
  
  assert (fix_prop := innerfn_prop (S q) (embed (S q)) (sheafC_sheaf (S q))
                                   (embed (S q)) (subp_embed (embed q)) 
                                   (exist (P := fun x => secondinnerinnerfnprop (S q) (embed (S q)) (sheafC_sheaf (S q)) (embed (S q)) x) (λ s1 : subp (S q), (` f) {Σ ` s1}) (λ s1 : subp (S q), (proj2_sig f) {Σ ` s1}))).
  simpl in fix_prop.
  unfold innerfn in fix_prop; simpl in fix_prop.
  rewrite lift_subp_rect_aux with (prf':= Le.le_refl q : q <= q).
  symmetry.
  apply fix_prop.
Qed.
  
Forcing Operator T : Type.
Next Obligation of T_inst.
  red. exact sheafC_sheaf.
Defined.

Forcing Operator U : Type.
Next Obligation of U_inst.
  red. exact sheafC_sheaf.
Defined.

Forcing Operator later_arrow : (later (T -> T) -> (later T -> later T)).
Next Obligation.
  red; simpl; intros; red in H.
  apply (H (iota r1) s1 arg1).
Qed.

Next Obligation.
  red.
  split; red; intros.
  reflexivity.
  reflexivity.
Qed.

Next Obligation.
  red; simpl; intros; red in H.
  apply (H (iota r3) s2 arg2).
Qed.

Next Obligation.
  red.
  split; red; intros.
  reflexivity.
  reflexivity.
Qed.

Lemma zero p : Psub p 0.
forcing.
Qed.

Definition elim_subp0 (P:subp 0 -> Type) (P0 : P (subp0 0)) : forall (q:subp 0), P q.
Proof. destruct q as [[|q] Hq].
  apply P0.
  red in Hq. elimtype False. inversion Hq.
Defined.

Definition elim_subp0P (P:subp 0 -> Prop) (P0 : P (subp0 0)) : forall (q:subp 0), P q.
Proof.  
  destruct q as [[|q] Hq].
  apply P0.
  red in Hq. elimtype False. inversion Hq.
Defined.

Definition later_arrow_sheaf_0 p : later_arrow_transty7 p (embed p) {Σ 0,zero p} (embed 0).
Proof. 
  refine (elim_subp0 _ _).
  intro.
  exact tt.
Defined.

Definition later_arrow_sheaf_Sq p q (Hq : Psub p (S q)) (arg : ∀ r : subp (embed q), sheaf r → sheaf r): later_arrow_transty7 p (embed p) {Σ S q,Hq} (embed (S q)).
Proof. 
  red; intros r arg'.
  destruct r as (r,Hr); destruct r.
  exact tt.
  assert (Psub q r) by forcing.
  exact (arg {Σ r,H} arg').
Defined.

Lemma succ_le r : Psub (S r) r.
Proof. forcing. Qed.

  Definition later_arrow_sheaf p : later_arrow_transty8 p (embed p).
  red; intros q arg.
  destruct q as (q,Hq); destruct q; simpl in *.
  exists (later_arrow_sheaf_0 p).

  intros r s arg'.
  destruct r as (r,Hr); assert (r = 0) by forcing; subst.
  destruct s as (s,Hs); assert (s = 0) by forcing; subst.
  reflexivity.

  exists (later_arrow_sheaf_Sq p q Hq (`arg)).

  intros r s arg'.
  destruct s as (s,Hs); destruct s.
  reflexivity.
  destruct r as (r,Hr); destruct r.
  assert (S s = 0) by forcing; subst.
  inversion H.
  assert (Psub q r) by forcing.
  assert (Psub r s) by forcing.
  apply ((proj2_sig arg) {Σ r,H} {Σ s,H0} arg').
  Defined.
  

  Lemma equal_exist {A} {P : A -> Prop} {p q : A} {x : P p} {y : P q} : p = q ->
    exist p x = exist q y.
  Proof.
    intros. subst.
    reflexivity.
  Qed.

  Lemma later_arrow_axiom p : later_arrow_transprop2 p {Σ p} (later_arrow_sheaf p).
  red; intros.
  destruct r as (r,Hr); destruct r.
  destruct s as (s,Hs); assert (s = 0) by forcing; subst.
  reflexivity.
  destruct s as (s,Hs); destruct s.
  simpl.
  refine (equal_exist _).
  apply functional_extensionality_dep.
  refine (elim_subp0P _ _). reflexivity.
  simpl.
  refine (equal_exist _).
  apply functional_extensionality_dep.
  intro u.
  unfold later_arrow_transprop2_obligation_1; simpl.
  apply functional_extensionality_dep.
  intro arg'.
  destruct u as (u,Hu); destruct u.
  reflexivity.
  reflexivity.
  Qed.

  Next Obligation.
    red; simpl; intros.
    exists (later_arrow_sheaf p).
    apply later_arrow_axiom.
  Defined.

  Forcing Operator later_arrow' : ((later T -> later T) -> (later (T -> T))).
  Next Obligation.
    red; simpl; intros; red in H.
    apply (H (iota r1) s1 arg1).
  Qed.

  Next Obligation.
    red.
    split; red; intros.
    reflexivity.
    reflexivity.
  Qed.

  Next Obligation.
    red; simpl; intros; red in H.
    apply (H (iota r3) s2 arg2).
  Qed.

  Next Obligation.
    red.
    split; red; intros.
    reflexivity.
    reflexivity.
  Qed.

  Definition later_arrow'_sheaf_Sq p q (Hq : Psub p (S q)) (arg : later_arrow'_transty3 p p
    (exist (S q) Hq) (embed (S q))) : later_arrow'_transty7 p (embed p) (exist (S q) Hq) (exist q (succ_le q)).
  red; intros r arg'.
  red in arg.
  apply (arg (subp_succ r) arg').
  Defined.
  
  Definition later_arrow'_sheaf p : later_arrow'_transty8 p (embed p).
  red; intros q arg.
  destruct q as (q,Hq); destruct q; simpl in *.
  exact tt.
  exists (later_arrow'_sheaf_Sq p q Hq (`arg)).
  intros r s arg'.
  apply ((proj2_sig arg) (subp_succ r) (subp_succ s) arg').
  Defined.
  
  Lemma later_arrow'_axiom p : later_arrow'_transprop2 p {Σ p} (later_arrow'_sheaf p).
    red; intros.
    destruct r as (r,Hr); destruct r.
    destruct s as (s,Hs); assert (s = 0) by forcing; subst.
    reflexivity.
    destruct s as (s,Hs); destruct s.
    reflexivity.
    reflexivity.
  Qed.

  Next Obligation.
    red; simpl; intros.
    exists (later_arrow'_sheaf p).
    apply later_arrow'_axiom.
  Defined.



  Forcing
  Lemma later_arrow_comm :  (forall (f:later(T->T)), eqf (later (T -> T)) (later_arrow' (later_arrow f)) f).

  Next Obligation.
    red; simpl; intros; red in H.
    apply (H (iota r1) s1 arg1).
  Qed.

  Next Obligation.
    red.
    split; red; intros.
    reflexivity.
    reflexivity.
  Qed.

  Next Obligation.
    red; simpl; intros.
    red; simpl; intros q arg.
    destruct q as (q,Hq); destruct q; red; simpl; intro r.
    reflexivity.
    reflexivity.
  Qed.

  Forcing
  Lemma later_arrow_comm' :  (forall (f:later T-> later T), eqf (later T -> later T) (later_arrow (later_arrow' f)) f).

  Next Obligation.
    red; simpl; intros; red in H.
    apply (H (iota r1) s1 arg1).
  Qed.

  Next Obligation.
    red.
    split; red; intros.
    reflexivity.
    reflexivity.
  Qed.

  Next Obligation.
    red; simpl; intros.
    red; simpl; intros q arg.
    destruct q as (q,Hq); destruct q; red; simpl; intro r.
    unfold Θ; simpl.
    apply equal_exist.
    apply functional_extensionality_dep.
    simpl.
    destruct r as (r,Hr); assert (r = 0) by forcing; subst.
    intro s; destruct s as (s,Hs); assert (s = 0) by forcing; subst.
    reflexivity.
    unfold Θ; simpl.
    apply equal_exist.
    apply functional_extensionality_dep.
    simpl; intro s.
    destruct arg as (arg,Harg).
    unfold later_arrow_comm'_transprop in Harg; simpl.
    apply functional_extensionality; intro arg'.
    destruct s as (s,Hs); destruct s.
    reflexivity.
    reflexivity.
  Qed.
  
  (* proofs of the following four axioms should be eq_refl *)
  Fixpoint nlater n T := match n with
                           | 0 => T
                           | S n' => later (nlater n' T)
                         end.

  Forcing
  Lemma next_naturality : (forall  (f:T -> T) (v:T), eqf (later T) (next T (f v)) ((next_arrow f) (next T v))).
  
  Next Obligation.
    red; simpl; intros; red in H.
    apply (H (iota r1) s1 arg1).
  Qed.

  Next Obligation.
    red.
    split; red; intros.
    reflexivity.
    reflexivity.
  Qed.

  Next Obligation.
    red; simpl; intros; red in H.
    apply (H (iota r4) s3 arg3).
  Qed.


  Next Obligation.
    red.
    split; red; intros.
    reflexivity.
    reflexivity.
  Qed.

  Next Obligation.
    red; intro.
    red; intros.
    destruct r as (r,Hr); destruct r.
    refine (elim_subp0P _ _).
    intro; simpl.
    intro; reflexivity.

    red; intros; simpl.
    destruct r3 as (r3,Hr3); destruct r3.
    simpl.
    intro; reflexivity.
    intro; unfold Θ; simpl.
    apply f_equal.
    assert (Psub (S r) (S r3)) by forcing.
    apply ((proj2_sig arg) (exist (S r3) H)).
  Qed.
  
  Forcing Operator idf : (forall T, T -> T).

  Next Obligation.
    red; simpl; intros; red in H.
    apply (H (iota r1) s1 arg1).
  Qed.

  Next Obligation.
    red.
    split; red; intros.
    reflexivity.
    reflexivity.
  Qed.
  
  Definition idf_sheaf p : idf_transty5 p (embed p).
  red; intros q arg.
  exists (fun (r:subp q) => fun (arg':sheaf_f arg r) => arg').
  red; intros r s arg'.
  reflexivity.
  Defined.

  Next Obligation.
    red; intro.
    exists (idf_sheaf p).
    red; intros; reflexivity.
  Defined.

  Forcing
  Lemma next_arrow_id : (eqf (later T -> later T) (next_arrow (idf T)) (idf (later T))).

  Next Obligation.
    red; simpl; intros; red in H.
    apply (H (iota r) s arg).
  Qed.

  Next Obligation.
    red.
    split; red; intros.
    reflexivity.
    reflexivity.
  Qed.

  Next Obligation.
    red; simpl; intros; red in H.
    apply (H (iota r2) s1 arg1).
  Qed.

  Next Obligation.
    red.
    split; red; intros.
    reflexivity.
    reflexivity.
  Qed.

  Next Obligation.
    red; simpl; intros; reflexivity.
  Qed.

  Next Obligation.
    red; intro p; destruct p; simpl.
    refine (elim_subp0P _ _).
    unfold Θ; simpl.
    apply equal_exist.
    apply functional_extensionality_dep.
    refine (elim_subp0P _ _).
    simpl. reflexivity.

    intro q.
    unfold Θ; simpl.
    apply equal_exist. simpl.
    apply functional_extensionality_dep. intro r; simpl.
    apply functional_extensionality_dep. intro arg; simpl.
    destruct r as (r,Hr); destruct r; simpl; reflexivity.
  Qed.


  Notation next_arrow f := (later_arrow (next (T -> T) f)).
  Notation comp g f := (fun x => g (f x)).
  
  Forcing
  Lemma next_arrow_comp : (forall (g:T->T) (f:T->T) (x:later T), eqf (later T)
    (next_arrow (comp g f) x) ((next_arrow g) ((next_arrow f) x))).

  Next Obligation of next_arrow_comp_transty.
  Proof.
    red; intros.
    red in H. simpl in *.
    apply (H (iota r1) s1 arg1).
  Qed.

  Next Obligation of next_arrow_comp_transty.
  Proof.
    red; intros.
    split; red; intros; reflexivity.
  Qed.

  Next Obligation of next_arrow_comp_transty5.
  Proof.
    red; intros.
    red in H. simpl in *.
    apply (H (iota r4) s3 arg3).
  Qed.

  Next Obligation of next_arrow_comp_transty5.
  Proof.
    red; intros.
    split; red; intros; reflexivity.
  Qed.


  Next Obligation of next_arrow_comp_transty11.
  Proof.
    red; intros. simpl in *.
    apply (H (iota r7) s5 arg5).
  Qed.

  Next Obligation of next_arrow_comp_transty11.
  Proof.
    red; intros; split; red; intros; reflexivity.
  Qed.

  Next Obligation of next_arrow_comp_transty11.
  Proof.
    red; intros. simpl in *. red in H0, arg2, H.
    destruct (sheafC_trans (iota s5)). red in H1.
    rewrite H1.
    destruct (sheafC_trans (` r7)). red in H3.
    rewrite H3.
    pose (H0 (iota r7)). simpl in e.
    rewrite e.
    apply f_equal. clear e H1 H2 H3 H4.
    simpl in *. pose (H (iota r7)). simpl in e.
    rewrite e. reflexivity.
  Qed.

  Next Obligation of next_arrow_comp_transty11.
  Proof.
    red; intros; simpl in *.
    apply (H (iota r9) s6 arg6).   Qed.

  Next Obligation of next_arrow_comp_transty11.
  Proof.
    red; intros; split; red; intros; reflexivity.
  Qed.


  Next Obligation of next_arrow_comp_transty11.
  Proof.
    red; intros; simpl in *.
    apply (H (iota r11) s7 arg7).   
  Qed.

  Next Obligation of next_arrow_comp_transty11.
  Proof.
    red; intros; split; red; intros; reflexivity.
  Qed.

  Next Obligation. 
  Proof.
    red. red; intros.
    red; intros.
    unfold next_arrow_comp_transty21. destruct r6.
    simpl. destruct x; simpl. red in p0.
    intro. red in arg4. red. simpl; reflexivity.
    
    intros arg4; red in arg4. simpl in arg4.
    red. reflexivity.
  Qed.

  Forcing
  Lemma next_arrow_wird : (forall (M : forall n, nlater n T -> nlater n T -> nlater n T)
    (n:nat) (g : nlater n T),
    later_arrow ((next_arrow (M n)) (next g)) = M (S n) (next g)).
