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

Program Inductive eqf_sheaf {p} : forall (q:subp p) (A:sheaf q) (r : subp q) (x : sheaf_f A r)
  (s : subp r) (y : sheaf_f A (ι s)) (t:subp s), Prop :=
| eqf_refl : forall (q:subp p) (A:sheaf q) (r : subp q) (x : sheaf_f A r) (s : subp r) (t:subp s),
     eqf_sheaf q A s (Θ A r s x) (ι s) (Θ A r s x) t.

Lemma eqf_sheaf_destruct2 {p}  (q:subp p) A r x s y t : eqf_sheaf q A r x s y t -> (ι r = s /\ Θ A r s x = y).
Proof.
  intro H; destruct H; split. reflexivity.
  destruct A as (A_f,AΘ); simpl.
  destruct AΘ as (AΘ,(Arefl,Atrans)); unfold Θ; simpl.
  assert (foo := Atrans r s (ι s) x); apply foo.
Qed.

Program Definition eqf_transp {p} (q:subp p) (A:sheaf q) (r : subp q) (x : sheaf_f A r)
  (s : subp r) (y : sheaf_f A (ι s)) : transport (eqf_sheaf q A r x s y).
unfold transport, arrow; intros.
destruct H; apply eqf_refl.
Defined.

Definition eqf_sheaf_f_1 {p} (q:subp p) (A : sheaf q) (r : subp q) (x : sheaf_f A r) :
  eqf_transty6 p {Σ p, le_refl p} q A (ι q) r (ι r).
red; intros s y.
exists (eqf_sheaf q A r x s y).
exists (eqf_transp q A r x s y).
split; red; intros; destruct x0; reflexivity.
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
intros r x; unfold eqf_transprop; simpl.
exists (eqf_sheaf_f_1 q A r x); intros s t y.
unfold eqf_sheaf_f_1, eqf_transp.
unfold sheafC; simpl.
(* destruct A as (A_f,AΘ); simpl. *)
(* destruct AΘ as (AΘ,(Arefl,Atrans)); simpl. *)
unfold Θ; simpl.

assert (foo : (λ s0 : subp t, eqf_sheaf q A r x s y (ι s0)) = 
(eqf_sheaf q A r x (ι t) ((` (projT2 A)) (ι s) (ι t) y))).
apply functional_extensionality; intro u.
apply prop_ext.
split; intros.
apply eqf_sheaf_destruct2 in H; destruct H as (Hrs,Hxy).
rewrite <- Hxy; destruct Hxy.
destruct A as (A_f,AΘ); simpl.
destruct AΘ as (AΘ,(Arefl,Atrans)); simpl.
setoid_rewrite (Atrans r s t x).
assert (foo := eqf_refl q (ΣA_f, {Σ AΘ}) r x (ι t) u). 
apply foo.

assert (foo := eqf_sheaf_destruct2 _ _ _ _ _ _ _ H).
rewrite <- foo in H. 
assert (foo2 := eqf_sheaf_destruct q A r x (ι t) u H s  (ι u)).
apply foo.
 _ _ _ _ (ι t) (ι u) H).
rewrite <- foo in H; clear foo.
apply eqf_sheaf_destruct with (s':=s) (t':=u) in H.
apply H.

rewrite <- H; clear H y.
destruct A as (A_f,AΘ); simpl.
destruct AΘ as (AΘ,(Arefl,Atrans)); simpl.
setoid_rewrite (Atrans r s t x).
apply eqf_refl.



subst; simpl in *.
destruct s0 as [s0 Hs0].
destruct t0 as [t0 Ht0].
simpl in *.
clear H4 H6 H9.
assert (foo' := foo (subp s0) (subp s0) {Σ s0, le_refl s0} {Σ s0,le_refl s0} {Σ s0,le_refl s0} s H5).
assert  foo in H5.
assert ( s0 = `s).
clear - H5.
assert (foo' := foo (subp s0) (subp s0) {Σ s0, le_refl s0} {Σ s0,le_refl s0} {Σ s0,le_refl s0} s).
apply foo' in H5.
induction H5.
intuition.
apply foo in H3.

generalize s x t y u.
inversion H.
subst; simpl in *.
apply (foo _ _) in H5.
simpl in *.
subst.
assert (x = Θ A r0 s0 x0).
intuition.
rewrite H0 in H.

intuition.
destruct H5.
assert (y = Θ A r0 s0 x0).
destruct s as [s Hs].
destruct t as [t Ht].
destruct u as [u Hu].
simpl.
elim H3.
subst.
apply eqf_refl.
induction H.
destruct y.

rewrite H; simpl;
rewrite <- (Atrans {Σ s} {Σ t} {Σ u});
reflexivity.


assert (foo : (λ s0 : subp t, ∀ u : subp s0, AΘ r (ι u) x = AΘ {Σ ` s} {Σ ` u} y) = 
(λ t0 : subp t, ∀ u : subp t0, AΘ r (ι u) x = AΘ (ι t) {Σ ` u} (AΘ (ι s) (ι t) y))).
apply functional_extensionality; intro.
apply prop_ext.
destruct s as [s Hs].
destruct t as [t Ht].
split; intros; destruct u as [u Hu];
rewrite H; simpl;
rewrite <- (Atrans {Σ s} {Σ t} {Σ u});
reflexivity.

destruct s as [s Hs].
destruct t as [t Ht].
simpl.

rewrite (equal_existT2 foo).



