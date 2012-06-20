Require Import Forcing.
Require Import RelationClasses.
Require Import eqf_ind.
Require Import Le.

Import NatForcing.
Import NatCondition.
Open Scope forcing_scope.

Obligation Tactic := program_simpl; forcing.
Notation " '{Σ'  x } " := (exist x _).

Forcing Operator natf : Set.

Inductive natf_sheaf_ind (q:nat) : Type :=
| zerof : natf_sheaf_ind q 
| succf : natf_sheaf_ind q -> natf_sheaf_ind q.

Definition natf_sheaf {p} : subp p -> Type := fun q => forall (r : subp q), natf_sheaf_ind (`r).

Program Definition natf_transp {p} : transport (natf_sheaf (p:=p)).
unfold transport, arrow; intros q r n r0.
specialize (n (ι r0)); apply n.
Defined.

Program Definition natf_transp_prop {p} : trans_prop (natf_transp (p:=p)).
Proof. split; red; intros; reflexivity. Qed.

Next Obligation.
intro p; exists (natf_sheaf (p:=p)).
exists (natf_transp (p:=p)).
exact natf_transp_prop.
Defined.

Opaque natf_sheaf.
Opaque natf_transp.

Forcing Operator Succf : (natf -> natf).
Next Obligation.
  red. intros.
  exists (λ (q:subp p) (n : natf_sheaf (ι q)) (r:subp q), succf (`r) (n r)).
  intros. red.
  reflexivity.
Defined.

Forcing Operator Zerof : natf.
Next Obligation.
  red. intros; exact (λ (q:subp p), zerof (`q)).
Defined.

Forcing 
Lemma zero_refl : (eqf natf Zerof Zerof).
Next Obligation.
  red. intros. red. reflexivity.
Qed.

Forcing 
Lemma succrefl : (forall x : natf, eqf natf (Succf x) (Succf x)).
Next Obligation.
Proof.
  red. intros. red. simpl; intros.
  red. reflexivity. 
Qed.

Ltac forcing ::= 
  try solve [simpl; unfold Psub in *; auto 20 with arith forcing].

Forcing 
Lemma eqrefl : (forall A : Type, forall x : A, eqf A x x).
Next Obligation.
  reduce. simpl. reflexivity.
Qed.

Forcing 
Lemma eqsucc : (forall x y : natf, eqf natf x y -> eqf natf (Succf x) (Succf y)).
Next Obligation.
  Transparent natf_transp natf_sheaf.
  repeat (red; simpl; intros). 
  red in H. simpl in *.
  apply f_equal.
  extensionality r0.
  apply f_equal.
  specialize (H r0).
  unfold Θ in H. simpl in H.
  unfold natf_transp in *.
  simpl in *. 
  apply equal_dep_f with (iota r0) in H. assumption.
Qed.
