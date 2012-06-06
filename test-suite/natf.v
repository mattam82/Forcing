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

(* Forcing Operator natf : Set. *)

(* Definition natf_sheaf {p} : subp p -> Set := fun p => nat. *)

(* Program Definition natf_transp p : transport (natf_sheaf (p:=p)). *)
(* unfold transport, arrow; intros q r n. exact n. *)
(* Defined. *)

(* Next Obligation. *)
(* intro p; exists (natf_sheaf (p:=p)). *)
(* exists (natf_transp p). *)
(* abstract (split; red; intros; reflexivity). *)
(* Defined. *)
(* Opaque natf_sheaf. *)
(* Opaque natf_transp. *)
(* Forcing Operator Succf : (natf -> natf). *)
(* Next Obligation. *)
(*   red. intros.  *)
(*   exists (natf_transp p (iota_refl p)). *)
(*   Transparent natf_transp. *)
(*   red. reflexivity. *)
(* Defined. *)
(* Opaque natf_transp. *)


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

Program Lemma natf_transp_prop p : trans_prop (natf_transp p).
split; red; intros; induction x.
reflexivity.
simpl; rewrite IHx; reflexivity.
reflexivity.
simpl; rewrite <- IHx; reflexivity.
Qed.
Set Printing Implicit.
Next Obligation.
intro p; exists (natf_sheaf (p:=p)).
exists (natf_transp p).
exact (natf_transp_prop p).
Defined.

Opaque natf_transp.

Implicit Arguments forcing_traduction [[A] [ForcingOp]].

Forcing Operator Zerof : natf.

Next Obligation.
intro p. exact (zerof (embed p)).
Defined.
Unset Printing Notations.
Unset Implicit Arguments. 
Definition Succf_transty := (fun (p : nat) (q : subp p) (r : subp q) =>
   @existT (forall _ : subp r, Type (* Top.220 *))
     (fun sheaf_f0 : forall _ : subp r, Type (* Top.222 *) =>
      @sig (@transport r sheaf_f0) (@trans_prop r sheaf_f0)) 
     (@natf_sheaf r)
     (@exist (@transport r (@natf_sheaf r)) (@trans_prop r (@natf_sheaf r))
        (natf_transp r) (natf_transp_prop r))).

Program 
Definition succf_transty2 :=
  (fun (p : nat) (q : subp p) =>
     forall (r : subp q)
            (_ : @projT1 (forall _ : subp r, Type (* Top.252 *))
                  (fun sheaf_f0 : forall _ : subp r, Type (* Top.222 *) =>
                     @sig (@transport r sheaf_f0) (@trans_prop r sheaf_f0))
                  (@Succf_transty p q r)
                  (@exist P (Psub r) (@proj1_sig P (Psub q) r) _ (* [p, q, r] *))),
   @projT1 (forall _ : subp r, Type (* Top.257 *))
     (fun sheaf_f0 : forall _ : subp r, Type (* Top.238 *) =>
      @sig (@transport r sheaf_f0) (@trans_prop r sheaf_f0))
     (Succf_transty p q r)
     (@exist P (Psub r) (@proj1_sig P (Psub q) r) _ (* [p, q, r] *))).

Inductive phant (A : Type) (a : A) := p.
Program
Definition foo :=
  forall (p : nat) (q : subp p) (f : succf_transty2 p q),
  forall (r : subp q) (s : subp r)
    (arg : @projT1 _ _ (Succf_transty p q r) (iota_refl r)),
   phant _ (@projT2 _ _ (Succf_transty p q r) r s (f r arg)).

Program 
Definition rhs :=
  forall (p : nat) (q : subp p) (f : succf_transty2 p q),
  forall (r : subp q) (s : subp r)
    (arg : @projT1 _ _ (Succf_transty p q r) (iota_refl r)),
    phant _ ((@projT2 _ _ (Succf_transty p q r) (iota_refl r) s arg)).

Print rhs.

Program 
Definition fsdom :=
  forall (p : nat) (q : subp p) (f : succf_transty2 p q),
  forall (r : subp q) (s : subp r)
    (arg : @projT1 _ _ (Succf_transty p q r) (iota_refl r)),

@projT1 (forall _ : subp (one_trans p q r s), Type)
         (fun sheaf_f0 : forall _ : subp (one_trans p q r s), Type =>
          @sig (@transport (one_trans p q r s) sheaf_f0)
            (@trans_prop (one_trans p q r s) sheaf_f0))
         (Succf_transty p q (one_trans p q r s))
         s.

Eval compute in fsdom.
(*
       @natf_sheaf (let (a, _) := s in a)
         (@exist nat (fun q0 : nat => Peano.le q0 (let (a, _) := s in a))
            (let (a, _) := s in a)
            ((let (PreOrder_Reflexive, _) := le_pre in PreOrder_Reflexive)
               (let (a, _) := s in a)))
*)


Program Definition lhs_ty :=
forall (p : nat) (q : subp p) (f : succf_transty2 p q),
  forall (r : subp q) (s : subp r)
    (arg : @projT1 _ _ (Succf_transty p q r) (iota_refl r)),
    
  (@projT1 (forall _ : subp r, Type)
     (fun sheaf_f0 : forall _ : subp r, Type =>
      @sig (@transport r sheaf_f0) (@trans_prop r sheaf_f0))
     (Succf_transty p q r)
     (@iota
        (@exist P (Psub r) (@proj1_sig P (Psub q) r)
           (succf_transty2_obligation_2 p q r)) s r
        (@iota_pi_inv r
           (@exist P (Psub r) (@proj1_sig P (Psub q) r)
              (succf_transty2_obligation_2 p q r)) s))).

Definition rhs_ty :=
forall (p : nat) (q : subp p) (f : succf_transty2 p q),
  forall (r : subp q) (s : subp r)
    (arg : @projT1 _ _ (Succf_transty p q r) (iota_refl r)),
    

  (@projT1 (forall _ : subp r, Type)
     (fun sheaf_f0 : forall _ : subp r, Type =>
      @sig (@transport r sheaf_f0) (@trans_prop r sheaf_f0))
     (Succf_transty p q r)
     (@iota (iota_refl r) s r (@iota_pi_inv r (iota_refl r) s))).

Eval compute in lhs_ty.
Eval compute in rhs_ty.

Check (eq_refl : lhs_ty = rhs_ty).

Forcing Operator Succf : (natf -> natf).

Program Definition unitf_transp p : transport (fun (q:subp p) => unit).
red; intros; intro; exact tt.
Defined.

Forcing Operator unitf : Set.
Next Obligation.
intro p; exists (fun (q:subp p) => unit).
exists (unitf_transp p).
split; red; intros; destruct x; reflexivity.
Defined.
Set Printing All.
