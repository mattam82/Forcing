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

Next Obligation.
intro p; exists (natf_sheaf (p:=p)).
exists (natf_transp (p:=p)).
abstract (split; red; intros; reflexivity).
Defined.

Opaque natf_sheaf.
Opaque natf_transp.

Forcing Operator Succf : (natf -> natf).
Next Obligation.
  red. intros.
  exists (λ (q:subp p) (n : natf_sheaf (ι q)) (r:subp q), succf (`r) (n r)).
  red; simpl; intros.
  extensionality s0. reflexivity.
Defined.

Forcing Operator Zerof : natf.
Next Obligation.
  red. intros; exact (λ (q:subp p), zerof (`q)).
Defined.

Forcing Operator eqf : (forall A, A -> A -> Prop).

Next Obligation.
red; simpl; intros.
apply (H (ι r2) s2 arg2).
Qed.

Next Obligation.
red; simpl; intros.
apply (H (ι r1) s1 arg1).
Qed.

Next Obligation.
  red. intros.
  refine (exist eqf_sheaf_f_3 _).
  admit. (* There must be a fast way to prove this *)
Qed.

Opaque eqf_sheaf.
Opaque eqf_transp.

Forcing Operator foo : (eqf natf Zerof Zerof).

Forcing Operator eqf_refl : (forall A, eqf Type A A).

Lemma foo: eqf natf (Succf Zerof) (Succf Zerof).



Forcing Operator foo : (eqf natf (Succf Zerof) Zerof).



