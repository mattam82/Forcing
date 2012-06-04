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

Forcing Operator natf : Set.

Inductive natf_sheaf {p} : subp p -> Type :=
| zerof : forall (q:subp p), natf_sheaf q
| succf : forall (q:subp p), natf_sheaf q -> natf_sheaf q.

Program Definition natf_transp p : transport (natf_sheaf (p:=p)).
unfold transport, arrow; intros q r n.
induction n.
apply (zerof (ι r)).
apply (succf (ι r) (IHn r)).
Defined.

Next Obligation.
intro p; exists (natf_sheaf (p:=p)).
exists (natf_transp p).
split; red; intros; induction x.
reflexivity.
simpl; rewrite IHx; reflexivity.
reflexivity.
simpl; rewrite <- IHx; reflexivity.
Defined.

Implicit Arguments forcing_traduction [[A] [ForcingOp]].

Forcing Operator Zerof : natf.

Next Obligation.
intro p. exact (zerof (embed p)).
Defined.

Program Definition unitf_transp p : transport (fun (q:subp p) => unit).
red; intros; intro; exact tt.
Defined.

Forcing Operator unitf : Set.
Next Obligation.
intro p; exists (fun (q:subp p) => unit).
exists (unitf_transp p).
split; red; intros; destruct x; reflexivity.
Defined.

(* Forcing Operator Succf : (natf -> natf). *)

