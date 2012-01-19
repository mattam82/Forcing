Require Import Forcing.
Require Import RelationClasses.

Definition proj_sub {p : nat} : subp p -> nat :=
  fun x => proj1_sig x.

Coercion ι_refl : subp >-> subp.

Hint Extern 0 (_ = _) => apply ι_ι_refl : forcing.
Hint Extern 0 (_ <= _) => apply reflexivity : forcing. 

Section Test.

  Variable p : nat.

  Force empty at p := (forall X : Set, X).

  Next Obligation. apply (proj2_sig (ι s)). Defined.
  Next Obligation. f_equal. 
    unfold ι, ι_refl. simpl. pi. Defined.

  Next Obligation. apply (proj2_sig (ι s)). Defined.
  Next Obligation. f_equal. 
    unfold ι, ι_refl. simpl. pi. Defined.

  Next Obligation. apply (proj2_sig (ι s)). Defined.

Obligation Tactic := program_simpl; eauto with forcing.

  Program Definition foo := (projT1 empty p).

  Force identity at p := (forall X : Set, X -> X).

  Eval hnf in foo.
    
apply (proj2_sig (ι s)). Defined.


Goal forall p : nat, True.  intros. 
(*   nat_force (forall X : Set, X) at p as foo. *)
Unset Printing Existential Instances.

(* Notation " '(Σ' x , y ) " := (exist _ x y). *)

Notation " t '=_{' p '}'  u " := (eq_type p t u) (at level 90).
Typeclasses eauto := debug 10.

  nat_force (forall X : Set, X) at p as foo.

  unfold proj1_sig in foo.

  
  Show Existentials.

Program Definition foo (p : nat) :=
(λ q : subp p,
      {f : ∀ (r : subp (P:=nat) (`q)) (X : sheaf (P:=nat) r), projT1 (sheafC (`r) r r X) r |
      ∀ (r : subp (P:=nat) q) (s : subp (P:=nat) r) (X : sheaf (P:=nat) r),
      f (ι s) (sheafC (`r) r s X) =_{ _ (* [p, q, f, r, s, X] *)}
      projT2 (sheafC (`r) r r X) r s (f r X)}).

  (λ q : subp (P:=nat) p,
    {f
      : ∀ (r : @subp nat nat_condition (`q))
      (X : sheaf (P:=nat) (`r)),
      sheaf_f (P:=nat) (sheafC (P:=nat) (`r) r r X) r
      | 
      ∀ (r : subp (P:=nat) (`q)) (s : subp (P:=nat) (`r))
      (X : sheaf (P:=nat) (`r)),
      let pr := proj1_sig (P:=fun x => le x (`q)) r in
      let sheaf := sheafC (P:=nat) pr r in
      let sheaf2 := sheafC (P:=nat) (`r) r r X in
        let fι := f (ι s) in
        let left := fι (sheaf s X) in
        let right := Θ sheaf2 r s (f r X) in
          left =_{ _ } right
            }).

Next Obligation.
  f_equal. 
  unfold ι, ι_refl. simpl. pi. 
Defined.
