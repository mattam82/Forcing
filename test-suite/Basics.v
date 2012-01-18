Require Import Forcing.

Goal forall p : nat, True.  intros. 
(*   nat_force (forall X : Set, X) at p as foo. *)

Program Definition foo (p : nat) :=
     (λ q : subp p,
      {f
      : ∀ (r : subp q)
        (X : sheaf r),
        sheaf_f (sheafC r r r X) r
      | True }).

      ∀ (r : subp q) (s : subp r)
      (X : projT1 (pairT (λ q0 : subp r, sheaf q0) (sheafC r)) r),
      f s (projT2 (pairT (λ q0 : subp r, sheaf q0) (sheafC r)) r s X) =
      projT2 (projT2 (pairT (λ q0 : subp r, sheaf q0) (sheafC r)) r r X) r s
        (f r X)}).

  Program Definition foo (p : nat) :=
     (λ (q : subp p),
       {f : forall (r : subp (` q))
         (X : sheaf (P:=nat) r),
         sheaf_f (sheafC (`r) r r X) r
      |
      ∀ (r : subp (`q)) (s : subp r)
      (X : sheaf (P:=nat) r),
      f s (sheafC (`r) r s X) =
      Θ (sheafC (`r) r r X) r s (f r X)}).

Program Definition foo (p : nat) :=
     (λ q : subp p,
      {f
      : ∀ (r : subp q)
        (X : sheaf r),
        projT1 (sheafC r r r X) r
      |
      ∀ (r : subp q) (s : subp r)
      (X : sheaf r),
      f s (sheafC r r s X) =
      projT2 (sheafC r r r X) r s (f r X)}).


Program Definition foo (p :nat) :=
  ((λ q : subp p,
    {f
    : ∀ (r : subp q) (X : sheaf r),
      sheaf_f _ (sheafC r r r X) r |
    ∀ (r : subp q) (s : subp r)
    (x : fst (λ q0 : subp r, sheaf q0, sheafC r) r),
    f s (snd (λ q0 : subp r, sheaf q0, sheafC r) r s x) =
    Θ (snd (λ q0 : subp r, sheaf q0, sheafC r) r r x) r s (f r x)})).

  nat_force (forall X : Set, X) at p as foo.
