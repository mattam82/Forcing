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

Program Definition eqf_sheaf {p} := fun (q:subp p) (A:sheaf q) (r : subp q) (x : sheaf_f A r)
  (s : subp r) (y : sheaf_f A (ι s)) (t : subp s) => forall (u: subp t), eq (Θ A r u x) (Θ A s u y).

Program Definition eqf_transp {p} (q:subp p) (A:sheaf q) (r : subp q) (x : sheaf_f A r)
  (s : subp r) (y : sheaf_f A (ι s)) : transport (eqf_sheaf q A r x s y) := λ q0 r0 H u, H u.

Definition eqf_sheaf_f_1 {p} (q:subp p) (A : sheaf q) (r : subp q) (x : sheaf_f A r) :
  eqf_transty6 p {Σ p, le_refl p} q A (ι q) r (ι r).
red; intros s y.
exists (eqf_sheaf q A r x s y).
exists (eqf_transp q A r x s y).
split; red; reflexivity.
Defined.

Lemma equal_exist2 {A} {P : A -> Prop} {p q: A} {x : P p} (H: p = q) : exist p x = exist q (eq_rect p _ x q H).
Proof.
destruct H.
replace (eq_rect p P x p eq_refl) with x; reflexivity.
Defined.

Lemma equal_existT2 {A} {P : A -> Type} {p q: A} {x : P p} (H: p = q) : existT p x = existT q (eq_rect p _ x q H).
Proof.
destruct H; reflexivity.
Defined.

Lemma equal_existT3 {A} {P : Type} {p q: A} {x : P} (H: p = q) : existT p x = existT q x.
Proof.
destruct H; reflexivity.
Defined.

Require Import FunctionalExtensionality.
Require Import ClassicalFacts.

Axiom prop_ext : prop_extensionality.

Program Definition eqf_sheaf_f_2 {p} (q:subp p) (A : sheaf q): eqf_transty7 p {Σ p, le_refl p} q A (ι q).
red; intros r x; unfold eqf_transprop; simpl.
exists (eqf_sheaf_f_1 q A r x); intros s t y.
destruct A as (A_f,AΘ); simpl.
destruct AΘ as (AΘ,(Arefl,Atrans)); simpl.
unfold eqf_sheaf_f_1, eqf_transp, eqf_sheaf.
unfold sheafC; simpl.
unfold Θ; simpl.

assert (foo : (λ s0 : subp t, ∀ u : subp s0, AΘ r (ι u) x = AΘ {Σ ` s} {Σ ` u} y) =
(λ t0 : subp t, ∀ u : subp t0, AΘ r (ι u) x = AΘ (ι t) {Σ ` u} (AΘ (ι s) (ι t) y))).
unfold trans in Atrans.

apply functional_extensionality; intro u.
apply prop_ext; split; intros H v; rewrite H.
destruct r as [r Hr].
destruct s as [s Hs].
destruct t as [t Ht].
destruct u as [u Hu].
assert (Hsq : s <= `q).
eapply le_trans; eassumption.
destruct v as [v Hv]; simpl.
assert (Hvt : v <= t).
eapply le_trans; eassumption.
setoid_rewrite (Atrans {Σ s,Hsq} {Σ t,Ht} {Σ v,Hvt}).
reflexivity.

destruct r as [r Hr].
destruct s as [s Hs].
destruct t as [t Ht].
destruct u as [u Hu].
assert (Hsq : s <= `q).
eapply le_trans; eassumption.
destruct v as [v Hv]; simpl.
assert (Hvt : v <= t).
eapply le_trans; eassumption.
setoid_rewrite (Atrans {Σ s,Hsq} {Σ t,Ht} {Σ v,Hvt}).
reflexivity.

assert (foo2 := {Σ
   λ (q0 : subp t) (r0 : subp q0)
   (H : ∀ u : subp q0, AΘ r (ι u) x = AΘ (ι t) {Σ ` u} (AΘ (ι s) (ι t) y))
   (u : subp r0), H {Σ ` u}} =
eq_rect (λ s0 : subp t, ∀ u : subp s0, AΘ r (ι u) x = AΘ {Σ ` s} {Σ ` u} y) _  {Σ
   λ (s0 : subp t) (t0 : subp s0)
   (x0 : ∀ u : subp s0, AΘ r (ι u) x = AΘ {Σ ` s} {Σ ` u} y)
   (u : subp t0), x0 {Σ ` u}}
   (λ t0 : subp t, ∀ u : subp t0, AΘ r (ι u) x = AΘ (ι t) {Σ ` u} (AΘ (ι s) (ι t) y))
   foo).

eapply eq_trans.
apply equal_existT2 with (H:=foo).
setoid_rewrite (Atrans {Σ s} {Σ t} {Σ u}).

unfold eqf_sheaf_f_1.
unfold sheafC; simpl.
unfold Θ; simpl.
destruct A as (A_f,AΘ); simpl.
Print eqf_sheaf.
destruct AΘ as (AΘ,(AProp,AProp2)); simpl.


