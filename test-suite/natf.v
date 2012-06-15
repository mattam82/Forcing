Require Import Forcing.
Require Import RelationClasses.
Require Import eqf_def.

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

Implicit Arguments forcing_traduction [[A] [ForcingOp]].

Notation " '{Σ' x } " := (exist x _).

Obligation Tactic := program_simpl; forcing.

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

Lemma equal_f {A B : Type} {f g : A -> B} : f = g -> forall x : A, f x = g x. 
Proof. now intros ->. Qed.

Lemma equal_dep_f {A} {B : A -> Type} {f g : ∀ x : A, B x} : f = g -> forall x : A, f x = g x. 
Proof. now intros ->. Qed.

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

Forcing 
Lemma eqrefl : (forall A : Type, forall x : A, eqf A x x).
Next Obligation.
  reduce. simpl. reflexivity.
Qed.
