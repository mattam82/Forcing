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
  reflexivity.
Defined.

Forcing Operator Zerof : natf.
Next Obligation.
  red. intros; exact (λ (q:subp p), zerof (`q)).
Defined.

(* Forcing Operator eqf : (forall A, A -> A -> Prop). *)

(* Next Obligation. *)
(* red; simpl; intros. *)
(* apply (H (ι r2) s2 arg2). *)
(* Qed. *)

(* Next Obligation. *)
(* red; simpl; intros. *)
(* split; red; intros. *)
(* reflexivity. *)
(* reflexivity. *)
(* Qed. *)

(* Next Obligation. *)
(* red; simpl; intros. *)
(* apply (H (ι r1) s1 arg1). *)
(* Qed. *)

(* Next Obligation. *)
(*   red. intros. *)
(*   split; red; intros; reflexivity. *)
(* Qed. *)

(* Next Obligation.   *)
(*   red; simpl; intros. *)
(*   refine (exist eqf_sheaf_f_3 _). *)
(*   red; intros. *)
(*   reflexivity. *)
(* Qed. *)

(* Opaque eqf_sheaf. *)
(* Opaque eqf_transp. *)

Existing Instance eqf_inst.
Print Instances ForcingOp.

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
  red. simpl.
  reflexivity. 
Qed.

Ltac forcing ::= 
  try solve [simpl; unfold Psub in *; auto 20 with arith forcing].

Forcing 
Lemma eqsucc : (forall x y : natf, eqf natf x y -> eqf natf (Succf x) (Succf y)).
Next Obligation.
Proof.
  simpl.
  unfold Psub.
  eauto 20 with forcing.
  red. intros. red. simpl; intros.
  red. simpl.
  reflexivity. 
Qed.





(* If producing commpi conditions for propositional sheafs, 
  we get the following:
*)

Program Definition succrefl_transty :=
  λ (p : nat) (q : subp p) (r : subp q), natf_inst_obligation_1 r.

Program Definition succrefl_transty1 :=
  λ (p : nat) (q : subp p) (r : subp q)
  (arg : projT1 (succrefl_transty p q r) r),
  eqf_sheaf_f_3 (iota_refl r) (natf_inst_obligation_1 r)
    (iota_refl r)
    (λ r0 : subp (iota_refl r),
     succf (` r0) (projT2 (succrefl_transty p q r0) r0 r0 arg r0))
    (iota_refl r)
    (λ r0 : subp (iota_refl r),
     succf (` r0) (projT2 (succrefl_transty p q r0) r0 r0 arg r0)).

Program Definition succrefl_transty2 :=
  λ (p : nat) (q : subp p),
  ∀ (r : subp q) (arg : projT1 (succrefl_transty p q r) r),
  (` (succrefl_transty1 p q r arg)) r.


Eval compute in
  λ (p : nat) (q : subp p) (f : succrefl_transty2 p q),
  λ (r : subp q) (s : subp r)
  (arg : projT1 (succrefl_transty p q r) (iota_refl r)),
     (f (iota s) (` (projT2 (succrefl_transty p q r)) (iota_refl r) s arg)).

Implicit Arguments eqf_sheaf [].

Eval simpl in ∀ (p : nat) (q : subp p),
       ∀ (r : subp q) (s : subp r)
         (arg : projT1 (succrefl_transty p q r) (iota_refl r)),
         (`
          (succrefl_transty1 p q (ι s)
             ((` (projT2 (succrefl_transty p q r))) (iota_refl r) s arg)))
           {Σ ` (ι s)}.
(* = ∀ (p : nat) (q : subp p) (r : subp q) (s : subp r)
       (arg : natf_sheaf (iota_refl r)),
       eqf_sheaf s (iota_refl s) (natf_inst_obligation_1 s) 
         (iota_refl s)
         (λ r0 : subp s,
          succf (` r0)
            (natf_transp {Σ ` r0} {Σ ` r0}
               (λ r1 : subp (` r0), natf_transp (iota_refl r) s arg {Σ ` r1})
               {Σ ` r0})) (iota_refl s)
         (λ r0 : subp s,
          succf (` r0)
            (natf_transp {Σ ` r0} {Σ ` r0}
               (λ r1 : subp (` r0), natf_transp (iota_refl r) s arg {Σ ` r1})
               {Σ ` r0})) {Σ s}
*)
Eval compute in
  λ (p : nat) (q : subp p) (f : succrefl_transty2 p q),
  λ (r : subp q) (s : subp r)
  (arg : projT1 (succrefl_transty p q r) (iota_refl r)),
     (proj2_sig (succrefl_transty1 p q r arg) (iota r) s (f r arg)).

Eval simpl in
 ∀ (p : nat) (q : subp p),
       succrefl_transty2 p q
       → ∀ (r : subp q) (s : subp r)
         (arg : projT1 (succrefl_transty p q r) (iota_refl r)),
         (` (succrefl_transty1 p q r arg)) (ι s).

(* 
     = ∀ (p : nat) (q : subp p),
       succrefl_transty2 p q
       → ∀ (r : subp q) (s : subp r) (arg : natf_sheaf (iota_refl r)),
         eqf_sheaf r (iota_refl r) (natf_inst_obligation_1 (` r))
           (iota_refl r)
           (λ r0 : subp r,
            succf (` r0)
              (natf_transp {Σ ` r0} {Σ ` r0}
                 (λ r1 : subp (` r0), arg {Σ ` r1}) 
                 {Σ ` r0})) (iota_refl r)
           (λ r0 : subp r,
            succf (` r0)
              (natf_transp {Σ ` r0} {Σ ` r0}
                 (λ r1 : subp (` r0), arg {Σ ` r1}) 
                 {Σ ` r0})) {Σ s}
*)

(* We seem to be comparing apples and oranges: 
  eqf_sheaf s <> eqf_sheaf r ,

however the definition of eqf_sheaf quantifies on a u, moving s and r in the 
same layer, hence the types are indeed definitionally equal (but it takes a 
while for Coq to see it).


*)

Definition foo :=
  ∀ (p : nat) (q : subp p)
    (f : succrefl_transty2 p q)
    (r : subp q) (s : subp r)
    (arg : projT1 (succrefl_transty p q r) (iota_refl r)),
    @eq_prop ((` (succrefl_transty1 p q r arg)) (ι s))
     (proj2_sig (succrefl_transty1 p q r arg) (iota r) s (f r arg))
     (f (iota s) (` (projT2 (succrefl_transty p q r)) (iota_refl r) s arg)).



Forcing Operator foo : (eqf natf (Succf Zerof) Zerof).



