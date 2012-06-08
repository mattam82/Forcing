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
pose (Atrans (iota s) (iota t) (iota v) y). apply e.
Defined.

Program Definition eqf_sheaf_f_3 {p} : eqf_transty8 p {Σ p, le_refl p}.
Proof.
  red; intros.
  exists (eqf_sheaf_f_2 (p:=p) r arg).
  red. simpl; intros.
  (* unfold eqf_sheaf_f_2. *)
  (* simpl. *)
  apply exist_eq.
  extensionality s2.
  (* unfold eqf_sheaf_f_1. *)
  extensionality y.
  apply exist_eq.
  unfold eqf_sheaf.
  extensionality t.
  apply prop_ext.
  split; intros.
  pose proof (sheaf_trans arg).
  red in H0.
  unfold compose in H0.
  rewrite (H0  (ι r1) s1 {Σ ` u} arg1).
  apply H.

  pose proof (sheaf_trans arg).
  red in H0.
  unfold compose in H0; simpl.
  specialize (H u). symmetry in H0.
  specialize (H0 r1 (iota s1)).
  simpl in H0.
  rewrite <- H0 in H; simpl in H.
  apply H.
Defined.

Next Obligation.
  red. intros.
  refine (exist eqf_sheaf_f_3 _).
  red; intros.
  on_call @eqf_sheaf_f_3 ltac:(fun c => pose proof (proj2_sig c)).
  symmetry. on_call @eqf_sheaf_f_3 ltac:(fun c => pose proof (proj2_sig c)).
  simpl. simpl in H. red in H.
  apply exist_eq. 
  admit. (* There must be a fast way to prove this *)
Qed.

(* Forcing Operator foobar : (eqf nat 0 1). *)


Lemma eqf_sheaf_destruct {p}  (q:subp p) A r x s y t : eqf_sheaf q A r x s y t -> (ι r = s /\ Θ A r s x = y /\ ι r = ι t).
Proof.
  intro H; destruct H; split; [reflexivity | split].
  destruct A as (A_f,AΘ); simpl.
  destruct AΘ as (AΘ,(Arefl,Atrans)); unfold Θ; simpl.
  assert (foo := Atrans r s (ι s) x); apply foo.
  reflexivity.
Qed.

Program Definition eqf_transp {p} (q:subp p) (A:sheaf q) (r : subp q) (x : sheaf_f A r)
  (s : subp r) (y : sheaf_f A (ι s)) : transport (eqf_sheaf q A r x s y).
unfold transport, arrow; intros.
apply  eqf_sheaf_destruct in H.
destruct H as (H1,(H2,H3)); subst. apply eqf_refl.
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
assert (foo := eqf_refl u). 
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



