Require Import Forcing.

Implicit Arguments projT1 [[A] [P]].
Implicit Arguments projT2 [[A] [P]].
Implicit Arguments existT [[A] [P]].

Goal forall p : nat, True.  intros. 

Program Definition foo (p : nat) :=
  fun q : @subp nat nat_condition p =>
      @sig
        (forall (r : @subp nat nat_condition q)
           (X : @projT1 _ _
                  (@existT _ _
                     (fun q0 : @subp nat nat_condition r =>
                      @sheaf nat nat_condition q0)
                     (@sheafC nat nat_condition r)) r),
         @projT1 _ _
          (@sheafC nat nat_condition (`r)
              r r X) r)
        (fun
           f : forall (r : @subp nat nat_condition q)
                 (X : @sheaf nat nat_condition r),
               @projT1 _ _
                 (@sheafC nat nat_condition r r r X) r => True).


         forall (r : @subp nat nat_condition q)
           (s : @subp nat nat_condition r)
           (X : @sheaf nat nat_condition r), True).


         @eq _
           (f s
              ((@sheafC nat nat_condition r) r s X))
           (f s
              ((@sheafC nat nat_condition r) r s X))).
(*            (@projT2 _ _ *)
(*               (@sheafC nat nat_condition r r r X) r s  *)
(*               (f r X))) *).

  nat_force (forall X : Set, X) at p as foo.
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
