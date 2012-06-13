Require Import Forcing.
Require Import RelationClasses.

Notation " '{Σ' x , y } " := (exist x y).
Notation " '(Σ' x , y ) " := (existT x y).

Import NatForcing.
Import NatCondition.
Open Scope forcing_scope.

Hint Extern 4 => progress (unfold le in *) : forcing.

Lemma subp_proof2 p (q : subp p) : ` q <= p. apply subp_proof. Defined.
Hint Resolve subp_proof2 : forcing.

Ltac forcing_le :=
  match goal with
    | |- le (@proj1_sig _ _ ?y) ?x => 
        apply (proj2_sig y)
    | |- ` ?x <= ?y => 
      match type of x with
        subp ?r => transitivity r
      end
    | |- le (@subp_proj ?x ?y) ?x => 
        apply (proj2_sig y)
    | |- subp_proj ?x <= ?y => 
      match type of x with
        subp ?r => transitivity r
      end
  end.

Hint Extern 2 (_ <= _) => forcing_le : forcing.

Obligation Tactic := program_simpl; forcing.

Program Definition embed (p : P) : subp p := p.

Notation " '{Σ'  x } " := (exist x _).

Require Import Le.
Notation ι r := (iota r).

Forcing Operator eqf : (forall A, A -> A -> Prop).

Next Obligation.
red; simpl; intros.
apply (H (ι r2) s2 arg2).
Qed.

Next Obligation.
red; simpl; intros.
apply (H (ι r1) s1 arg1).
Qed.

Program Inductive eqf_sheaf_ind {p:nat} (A:sheaf p) (x : sheaf_f A p) : (sheaf_f A (embed p)) -> Prop :=
| eqf_refl : eqf_sheaf_ind A x x.

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

Program Definition eqf_sheaf_f_2 {p} (q:subp p) (A : sheaf q): eqf_transty7 p {Σ p, le_refl p} q A (ι q).
red; intros r x. unfold eqf_transprop; simpl.
exists (eqf_sheaf_f_1 q A r x); intros s t y.
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
simpl in *.
setoid_rewrite <- e; apply eqf_refl.
red in Atrans.
pose (Atrans (iota s) (iota t) (iota v) y).
simpl in e.
setoid_rewrite <- e; apply eqf_refl.
Defined.

Program Definition eqf_sheaf_f_3 {p} : eqf_transty8 p {Σ p, le_refl p}.
Proof.
  red; intros.
  exists (eqf_sheaf_f_2 (p:=p) r arg).
  red. simpl; intros.
  apply exist_eq.
  extensionality s2.
  extensionality y.
  apply exist_eq.
  unfold eqf_sheaf.
  extensionality t.
  apply prop_ext.
  split; intros.
  pose proof (sheaf_trans arg).
  red in H0.
  unfold compose in H0.
  setoid_rewrite (H0  (ι r1) s1 (ι u) arg1).
  apply H.

  pose proof (sheaf_trans arg).
  red in H0.
  unfold compose in H0; simpl.
  specialize (H u). symmetry in H0.
  specialize (H0 r1 (iota s1)).
  simpl in H0.
  setoid_rewrite <- H0 in H; simpl in H.
  apply H.
Defined.

Next Obligation.
  red. intros.
  refine (exist eqf_sheaf_f_3 _).
  admit. (* There must be a fast way to prove this *)
Qed.
