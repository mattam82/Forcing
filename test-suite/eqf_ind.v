Require Import RelationClasses Le.
Require Import Forcing.
Import NatForcing.
Import NatCondition.
Open Scope forcing_scope.

Forcing Operator eqf : (forall A, A -> A -> Prop).

Next Obligation.
red; simpl; intros.
apply (H (ι r2) s2 arg2).
Qed.

Next Obligation.
red; simpl; intros.
split; red; intros.
reflexivity.
reflexivity.
Qed.

Next Obligation.
red; simpl; intros.
apply (H (ι r1) s1 arg1).
Qed.

Next Obligation.
red; simpl; intros.
split; red; intros.
reflexivity.
reflexivity.
Qed.

Inductive eqf_sheaf_ind {p:nat} (A:sheaf p) (x : sheaf_f A (embed p)) : (sheaf_f A (embed p)) -> Prop :=
| eqf_refl : eqf_sheaf_ind A x x.

Hint Resolve eqf_refl : core.

Instance eqf_sheaf_ind_refl p A : Reflexive (@eqf_sheaf_ind p A).
Proof eqf_refl A. 

Instance eqf_sheaf_ind_sym p A : Symmetric (@eqf_sheaf_ind p A).
Proof. red. now induction 1. Qed.

Instance eqf_sheaf_ind_trans p A : Transitive (@eqf_sheaf_ind p A).
Proof. red. now induction 1. Qed.

Instance eqf_sheaf_ind_equiv p A : Equivalence (@eqf_sheaf_ind p A) := {}.

Program Definition eqf_sheaf {p} := fun (q:subp p) {A:sheaf q} (r : subp q) (x : sheaf_f A r)
  (s : subp r) (y : sheaf_f A (ι s)) (t : subp s) => forall (u: subp t), 
    (eqf_sheaf_ind (sheafC p q (ι u) A) (Θ A r (ι u) x) (Θ A (ι s) (ι u) y)).

Program Definition eqf_transp {p} (q:subp p) (A:sheaf q) (r : subp q) (x : sheaf_f A r)
  (s : subp r) (y : sheaf_f A (ι s)) : prop_transport (eqf_sheaf q r x s y) := λ q0 r0 H u, H u.

Definition eqf_sheaf_f_1 {p} (q:subp p) (A : sheaf q) (r : subp q) (x : sheaf_f A r) :
  eqf_transty6 p {Σ p, le_refl p} q A (ι q) r (ι r).
red; intros s y.
exists (eqf_sheaf q r x s y).
exact (eqf_transp q A r x s y).
Defined.

Require Import FunctionalExtensionality.
Require Import ClassicalFacts.

Axiom prop_ext : prop_extensionality.

Lemma exist_eq {A : Type} {P : A -> Prop} (x y : A) (p : P x) (q : P y) : x = y -> exist x p = exist y q.
Proof. intros; subst; reflexivity. Qed.
Notation " '{Σ'  x } " := (exist x _).

Hint Extern 10 (Iota _ _ _) => progress (unfold iota; simpl) : typeclass_instances.

Program Definition eqf_sheaf_f_2 {p} (q:subp p) (A : sheaf q): eqf_transty7 p (embed p) q A (ι q) :=
          fun r x => eqf_sheaf_f_1 q A r x.

Next Obligation of eqf_sheaf_f_2.
Proof. 
  unfold eqf_transprop; simpl.
  intros s t y.
  apply exist_eq.
  unfold eqf_sheaf_f_1, eqf_transp, eqf_sheaf.
  unfold prop_sheafC; simpl.
  extensionality s0.
  apply prop_ext; split; intros H v; specialize (H v). 
  pose (sheaf_trans A (iota s) (iota t) (iota v) y).
  simpl in *.
  setoid_rewrite <- e in H.
  apply H.
  pose (sheaf_trans A (iota s) (iota t) (iota v) y).
  simpl in e.
  setoid_rewrite <- e. apply H.
Qed.

Program Definition eqf_sheaf_f_3 {p} : eqf_transty8 p (embed p) :=
          eqf_sheaf_f_2 (p:=p).
Next Obligation of eqf_sheaf_f_3.
Proof.
  red; intros.
  simpl; intros.
  apply exist_eq.
  extensionality s2.
  extensionality y.
  apply exist_eq.
  unfold eqf_sheaf.
  extensionality t.
  apply prop_ext.
  split; intros.
  pose proof (sheaf_trans x0).
  red in H0.
  unfold compose in H0.
  setoid_rewrite (H0  (ι r1) s1 (ι u) arg1).
  apply H.

  pose proof (sheaf_trans x0).
  red in H0.
  unfold compose in H0; simpl.
  specialize (H u). symmetry in H0.
  specialize (H0 r1 (iota s1)).
  simpl in H0.
  setoid_rewrite <- H0 in H; simpl in H.
  apply H.
Qed.

Next Obligation.
  red. intros.
  refine (exist eqf_sheaf_f_3 _).
  red; intros.
  reflexivity.
Defined.
