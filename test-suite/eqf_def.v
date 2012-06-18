Require Import Forcing.
Require Import RelationClasses.

Import NatForcing.
Import NatCondition.
Open Scope forcing_scope.

Hint Extern 4 => progress (unfold le in *) : forcing.
Obligation Tactic := program_simpl; forcing.

Notation " '{Σ'  x } " := (exist x _).

Require Import Le.

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

Program Definition eqf_sheaf {p} := fun (q:subp p) (A:sheaf q) (r : subp q) (x : sheaf_f A r)
  (s : subp r) (y : sheaf_f A (ι s)) (t : subp s) => forall (u: subp t), eq (Θ A r u x) (Θ A s u y).

Program Definition eqf_transp {p} (q:subp p) (A:sheaf q) (r : subp q) (x : sheaf_f A r)
  (s : subp r) (y : sheaf_f A (ι s)) : prop_transport (eqf_sheaf q A r x s y) := λ q0 r0 H u, H u.

Definition eqf_sheaf_f_1 {p} (q:subp p) (A : sheaf q) (r : subp q) (x : sheaf_f A r) :
  eqf_transty6 p {Σ p, le_refl p} q A (ι q) r (ι r).
red; intros s y.
exists (eqf_sheaf q A r x s y).
exact (eqf_transp q A r x s y).
Defined.

Require Import FunctionalExtensionality.

Require Import ClassicalFacts.
Axiom prop_ext : prop_extensionality.

Program Definition eqf_sheaf_f_2 {p} (q:subp p) (A : sheaf q): eqf_transty7 p {Σ p, le_refl p} q A (ι q) := 
          fun r x => eqf_sheaf_f_1 q A r x.

Next Obligation of eqf_sheaf_f_2.
unfold eqf_transprop; simpl.
intros s t y.
apply exist_eq.
destruct A as (A_f,AΘ); simpl.
destruct AΘ as (AΘ,(Arefl,Atrans)); simpl.
unfold eqf_sheaf_f_1, eqf_transp, eqf_sheaf.
unfold prop_sheafC; simpl.
unfold Θ; simpl.
simpl in *.
extensionality s0.
apply prop_ext; split; intros H v; rewrite H.
red in Arefl, Atrans. unfold compose in Atrans. 
pose (Atrans (iota s)).
specialize (e (iota t) (iota v) y).
symmetry in e. apply e.
red in Atrans.
pose (Atrans (iota s) (iota t) (iota v) y). apply e.
Qed.

Program Definition eqf_sheaf_f_3 {p} : eqf_transty8 p {Σ p, le_refl p} :=
          eqf_sheaf_f_2 (p:=p).

Next Obligation of eqf_sheaf_f_3.
Proof.
  red; intros.
  unfold eqf_sheaf_f_2.
  apply exist_eq. simpl.
  extensionality s2.
  extensionality y. simpl in *.
  unfold eqf_sheaf_f_1.

  apply exist_eq.
  unfold eqf_sheaf.
  extensionality t.
  apply prop_ext.
  split; intros.
  pose proof (sheaf_trans x0).
  red in H0.
  unfold compose in H0.
  simpl in *.
  rewrite (H0 (ι r1) s1 {Σ ` u} arg1).
  apply H.

  pose proof (sheaf_trans x0).
  red in H0.
  unfold compose in H0; simpl.
  specialize (H u). symmetry in H0.
  specialize (H0 r1 (iota s1)).
  simpl in *.
  rewrite <- H0 in H; simpl in H.
  apply H.
Qed.

Next Obligation.
  red. intros.
  refine (exist eqf_sheaf_f_3 _).
  abstract (red; intros; reflexivity).
Defined.
