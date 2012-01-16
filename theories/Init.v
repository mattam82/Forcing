Require Export Unicode.Utf8_core.
Require Export Coq.Program.Program.
Require Import Relations RelationClasses Setoid.

(** Basic definitions for forcing *)

(** Forcing conditions come with a preorder *)

Class Condition (A : Type) := {
  le : relation A ;
  le_pre :> PreOrder le ;
  le_pi : forall x y (p q : le x y), p = q
}.

Delimit Scope forcing_scope with forcing.

Notation " x <= y " := (le x y) : forcing_scope.

Require Import Le.
Instance nat_condition : Condition nat := {| le := Peano.le |}.
Proof. split; red; intros. apply le_n. eapply le_trans; eauto.
  intros. apply proof_irrelevance.
Qed.

Lemma eq_rect_irrel A (x : A) P (px : P x) y prf (py : P y) : 
  px = eq_rect y P py x (symmetry prf) -> eq_rect x P px y prf = py.
Proof.
  intros. destruct prf. simpl in *. exact H.
Qed.

Lemma eq_rect_f_equal {A B} (f : A -> B) (x y : A) (P : B -> Type) (p : P (f x)) (prf : x = y) :
  eq_rect (f x) P p (f y) (f_equal f prf) (* P (f y) *) =
  eq_rect x (fun x => P (f x)) p y prf.
Proof. destruct prf. simpl. reflexivity. Defined.

Lemma eq_trans_eq_refl_l {A} (x y : A) (p : x = y) : eq_trans eq_refl p = p.
Proof. destruct p. reflexivity. Defined.
  
Lemma eq_trans_eq_refl_r {A} (x y : A) (p : x = y) : eq_trans p eq_refl = p.
Proof. destruct p. reflexivity. Defined.

Lemma eq_rect_sym {A} {Q : A -> Type} (x y : A) (p : Q y) (prf : x = y) :
  eq_rect x Q (eq_rect y Q p x (eq_sym prf)) y prf = p.
Proof. destruct prf. simpl. reflexivity. Qed.

Lemma eq_rect_comm {A} {Q : A -> Type} (x y : A) (p : Q y) (prf : x = y) (prf' : y = x) :
  eq_rect x Q (eq_rect y Q p x prf') y prf = p.
Proof. replace prf' with (eq_sym prf) by apply proof_irrelevance. apply eq_rect_sym. Qed.

Lemma ext_eq_pointwise {A B} (f g : A -> B) (prf : f = g) (x : A) : f x = g x.
Proof. now subst f. Defined.
  
Lemma eq_rect_f {A B C} (f g : A -> B) (P : (A -> B) -> C -> Type) 
  (pf : forall C, P f C) (prf : f = g) (x : C) : 
  eq_rect f (fun f : A -> B => forall c, P f c) pf g prf x = 
  eq_rect f (fun f : A -> B => P f x) (pf x) g prf. 
Proof. destruct prf. simpl. reflexivity. Qed.
  
(* Lemma eq_rect_f {A B} (f g : forall x : A, B x) (P : (forall x : A, B x) -> Type)  *)
(*   (prf : f = g) (c : A) (pf : B c -> P f) : *)
(*   eq_rect f (fun f => arrow (f c) (P f)) pf g prf c. *)
(*   eq_rect f (fun f => P f x) (pf x) g prf.  *)
(* Proof. destruct prf. simpl. reflexivity. Qed. *)


Section Forcing.
  Context {P:Type} `{C : Condition P}.

  Local Open Scope forcing_scope.

  Definition subp (p : P) := { q : P | q <= p }.

  (** [subp] also forms valid forcing conditions *)

  Global Program Instance subp_cond p : Condition (subp p) := 
  { le x y := `x <= y }.

  Next Obligation.
  Proof. constructor; red. intro x; apply reflexivity.
    intros x y z; apply transitivity.
  Defined.

  Next Obligation.
  Proof. apply le_pi. Defined. 

  (** The injection from P_q to P_p with q <= p *)

  Program Definition ι' {p q} (sq : subp q) (π : q <= p) : subp p := sq.
  Next Obligation.
  Proof.  destruct sq. simpl. now transitivity q. Defined.

  Program Lemma subp_inj {p} (q : subp p) (r : subp q) : ` r <= p.
  Proof. intros. destruct q, r; simpl in *. now transitivity x. Defined.
    
  Program Lemma ι {p} {q : subp p} (r : subp q) : subp p.
  Proof. intros. exists (` r). destruct q, r; simpl in *. now transitivity x. Defined.

  Program Lemma ι_lift {p} {q : subp p} (r : subp q) : subp (ι r).
  Proof. intros. exists (` r). destruct r; reflexivity. Defined.

  Program Lemma ι_inj {p} {q : subp p} (r : subp q) : ` r = ` (ι r).
  Proof. intros. destruct r. simpl. unfold ι. simpl. destruct q. simpl. reflexivity. Defined.

  Definition ι_ι {p} {q : subp p} {r : subp (` q)} (s : subp (` r)) : subp (` (ι r)).
  Proof. exists (` s). rewrite <- ι_inj. apply (proj2_sig s). Defined.

  Program Lemma ι_refl {p} (q : subp p) : subp (` q).
  Proof. intros. exists (` q). reflexivity. Defined.

  Lemma ι_ι_refl {p} (q : subp p) : ι (ι_refl q) = q.
  Proof. unfold ι, ι_refl. simpl. destruct q. simpl. f_equal. apply le_pi. Defined.

  Hint Extern 0 (_ = _) => apply ι_ι_refl : forcing.
  Hint Extern 0 (_ <= _) => apply reflexivity : forcing. 
  Ltac prog_forcing := auto with forcing.
  Hint Extern 0 (_ = _) => try f_equal ; apply le_pi : forcing.

  Obligation Tactic := program_simpl ; prog_forcing.

  Lemma trans_refl_l (x y : P) (prf : x <= y) : transitivity (reflexivity x) prf = prf.
  Proof. apply le_pi. Defined.

  Section Translation.

    Definition transport {p} (f : subp p → Type) :=
      forall q : subp p, forall r : subp (` q), arrow (f q) (f (ι r)).

    Section Sheaf.
      Context {p} {f : subp p -> Type}.

      Notation " 'rewrite' p 'in' x " := (eq_rect _ _ x _ p) (at level 10).

      Program Definition refl (Θ : transport f) :=
        forall q : subp p, forall x : f q, 
          (rewrite (ι_ι_refl q) in (Θ q (ι_refl q) x)) = x.
      
      Program Definition trans (Θ : transport f) := 
        forall q : subp p, forall r : subp q, forall s : subp r,
          forall x, ((Θ (ι r) (ι_ι s)) ∘ (Θ q r)) x = Θ q (ι s) x.
    
      Next Obligation. unfold ι, ι_ι. simpl. f_equal. apply le_pi. Defined.

    End Sheaf.

(*     Record sheaf (p : P) := *)
(*       { sheaf_f : subp p → Type ;  *)
(*         Θ : transport sheaf_f ; *)
(*         sheaf_refl : refl Θ ; *)
(*         sheaf_trans : trans Θ }. *)

    Definition sheaf (p : P) :=
      { sheaf_f : subp p -> Type &
        { Θ : transport sheaf_f |
          refl Θ /\ trans Θ } }.

    Definition sheaf_f {p : P} (s : sheaf p) : subp p -> Type :=
      projT1 s.

    Program Definition Θ {p : P} (s : sheaf p) : transport (sheaf_f s) :=
      projT2 s.

    Definition sheaf_refl {p} (s : sheaf p) : refl (Θ s).
    Proof. unfold Θ. destruct s. destruct s. destruct a. simpl. assumption. Defined.

    Definition sheaf_trans {p} (s : sheaf p) : trans (Θ s).
    Proof. unfold Θ. destruct s. destruct s. destruct a. simpl. assumption. Defined.

    Program Definition sheafC (p : P) (q : subp p) (r : subp (` q)) 
      (f : sheaf (` q)) : sheaf (` r) :=
        existT _ (fun s => sheaf_f f (ι s))
        (λ s : subp (`r), λ t : subp (` s), λ x : sheaf_f f (ι s),
          (Θ f (ι s) (ι_ι t) x) : sheaf_f f (ι_ι t)).

    Next Obligation. intros. unfold ι, ι_ι; simpl. f_equal. apply le_pi. Defined.

    Notation " '(Σ' x , y ) " := (exist _ x y).

    Next Obligation. split. intros. 
      red. intros. destruct q0. simpl. rewrite eq_trans_eq_refl_l.
      unfold subp. simpl. unfold ι. simpl.
      rewrite eq_rect_f_equal.
      simpl. destruct r; simpl.
      unfold sheafC_obligation_1. simpl.
      rewrite eq_trans_eq_refl_l. simpl.
      rewrite eq_rect_f_equal. simpl.
      destruct f; simpl. 
      unfold ι_ι. simpl. 
      set(theprf :=
        (transitivity (x:=x0) (y:=x0) (z:=` q) (reflexivity x0)
          (transitivity (x:=x0) (y:=x1) (z:=` q) l l0))). abstract_eq_proofs.
      revert theprf eqH0 x.
      destruct eqH. subst l1. intros. simpl. 
      unfold ι in *. simpl in *. subst theprf.
      revert eqH0 x.
      rewrite (trans_refl_l x0 x1 l).
      set (ll0:=transitivity (x:=x0) (y:=x1) (z:=` q) l l0).
      clearbody ll0. intros.
      destruct s. destruct a as [re tr].
      red in re. 
      on_call @Θ ltac:(fun c => set (foo := c)).
      unfold ι in foo. simpl in *.
      pose (re (Σx0, ll0) x). rewrite <- e.
      unfold ι, ι_refl. simpl. rewrite eq_trans_eq_refl_l.
      rewrite eq_rect_f_equal. f_equal. pi.

      (* Trans *)
      pose (sheaf_trans f).
      match goal with [ |- trans (fun s t x => @?X s t x) ] => set(term:=X) end.
      unfold trans. intros.
      unfold trans_obligation_1; simpl.
      rewrite !eq_trans_eq_refl_l.
      unfold ι. simpl.
      rewrite eq_rect_f_equal. simpl. 
      destruct q0, r, r0, s; simpl in *. 
      unfold compose; subst term. simpl. 
      unfold sheafC_obligation_1. simpl.
      rewrite !eq_trans_eq_refl_l.
      unfold ι, ι_ι. simpl.
      rewrite !eq_rect_f_equal.
      set (theprf :=      (transitivity l2 (transitivity l1 l))).
      abstract_eq_proofs.
      destruct eqH1. simpl.
      set (theprf := (transitivity (transitivity (transitivity l2 l1) l) l0)) in *.
      destruct eqH2. simpl.
      set (theprf := (transitivity (transitivity l1 l) l0)) in *.
      destruct eqH0. simpl.
      specialize (t (Σx0, transitivity l l0) (Σ x2, l1) (Σ x3, l2) x).
      unfold ι, ι_ι in t. simpl in t. unfold compose in t.
      rewrite t. clear t.
      unfold trans_obligation_1. simpl.
      rewrite !eq_trans_eq_refl_l.
      rewrite eq_rect_f_equal.
      rewrite eq_rect_comm. reflexivity.
    Qed.

    (*
    Program Definition I_s (p : P) : sheaf p := {|
      sheaf_f q := sheaf (`q); 
      Θ := sheafC p |}.

    Lemma app_irrel {A} {Q : A -> Prop} 
      (B : Type) (f : sig Q -> B) 
      (x : sig Q) (prf : Q (`x)) : f x = f (Σ `x, prf).
    Proof. destruct x. f_equal. simpl. f_equal. pi. Qed.

    Lemma app_dep_irrel {A} {Q : A -> Prop} 
      (B : A -> Type) (f : forall x : sig Q, B (` x))
      (x : sig Q) (prf : Q (`x)) : f x = f (Σ `x, prf).
    Proof. destruct x. simpl in *. rewrite (proof_irrelevance _ q prf). reflexivity. Qed.

    Require Import Setoid Morphisms.

    Notation " 'rew' p 'in' x " := (eq_rect _ _ x _ p) (at level 10, only parsing).

    Lemma eq_sheafs (p : P) (x y : sheaf p) : 
      forall eq : sheaf_f p x = sheaf_f p y,
        rew eq in (Θ p x) = Θ p y -> x = y.
    Proof.
      destruct x, y; simpl.
      intros. destruct eq. simpl in *. subst Θ0. f_equal. pi. pi.
    Qed.
    
    Instance proper_extensionality {A} {B: Type} (f : A -> B) : 
      Proper (pointwise_relation A eq) f.
    Proof. intro. reflexivity. Defined.

    Instance proper_forall_eq {A} {B: A -> Type} (f : forall x : A, B x) :
      (forall (a : A) (R : relation (B a)), Proper R (f a)) ->
      Proper (forall_relation (fun x : A => eq)) f.
    Proof. intro. intro. reflexivity. Defined.

    Next Obligation.
    Proof. red. intros.
      unfold ι_ι_refl. 
      destruct q. simpl. rewrite eq_trans_eq_refl_l.
      unfold ι, ι_refl.
      rewrite eq_rect_f_equal. abstract_eq_proofs. destruct eqH.
      simpl in *.
      subst l0.
      assert(sheaf_f x0 (sheafC p (Σx0, l) (exist (fun x => x <= x0) x0 (reflexivity x0)) x) =
        sheaf_f x0 x).
      destruct x. simpl. extensionality y.
      symmetry ; apply app_irrel.
      symmetry. symmetry in H.
      apply eq_sheafs with H.
      destruct x. simpl in *.
      unfold sheafC_obligation_1.
      simpl.
      extensionality s. extensionality s'; extensionality s''.
      rewrite eq_trans_eq_refl_l. unfold ι. rewrite eq_rect_f_equal.
      destruct s, s'; simpl in *.
      unfold ι in *. simpl in *. 
      set (theprf:=         (transitivity (x:=x1) (y:=x0) (z:=x0)
            (transitivity (x:=x1) (y:=x) (z:=x0) l1 l0) 
            (reflexivity x0))) in *.
      unfold ι_ι. simpl.
      unfold transport.
      rewrite !eq_rect_f.
      assert((λ x, sheaf_f0 x) = sheaf_f0) by reflexivity.
      revert s''. 
      revert H Θ0 sheaf_refl0 sheaf_trans0. destruct H0. subst sheaf_f1.
      intros. subst theprf.
      abstract_eq_proofs. 
      assert(transitivity l0 (reflexivity x0) = l0). apply le_pi.
      assert 
        (Θ0 (Σx, l0) (Σx1, l1)
          (rew H0 in s'') = (Θ0 (Σx, transitivity (x:=x) (y:=x0) (z:=x0) l0 (reflexivity x0))
          (Σx1, l1))).
      

      revert s''.
      revert_until H. revert H.

      change (sheaf_f0
           (Σx, transitivity (x:=x) (y:=x0) (z:=x0) l0 (reflexivity x0))) with
      ((fun f => f
           (Σx, transitivity (x:=x) (y:=x0) (z:=x0) l0 (reflexivity x0))) 
      (fun x : subp x0 => sheaf_f0 x)).
      pattern (λ x : subp x0, sheaf_f0 x).
      
      Lemma eq_rect_f {Q B} (f g : sig Q -> B) (P : (sig Q -> B) -> Type) 
        (pf : P f) (prf : f = g) : 
        eq_rect (λ x, f x) P pf (λ x, g x) prf x = 
        eq_rect f (fun f : A -> B => P f x) (pf x) g prf. 
      Proof. destruct prf. simpl. reflexivity. Qed.

      pattern (transitivity l0 (reflexivity x0)).

revert s''.      
      rewrite H.
      
      

      destruct x.
      unfold sheafC. simpl.
      unfold ι. simpl. (* setoid_rewrite <- (app_irrel _ sheaf_f0) at 1. *)
      unfold sheafC_obligation_1. simpl. setoid_rewrite eq_trans_eq_refl_l.

      destruct x. simpl. unfold ι at 1. simpl.
      assert sheaf_f0 = (
      Set Printing All. idtac.
      Check (fun s : subp x0 => ι s).

      unfold ι. simpl. dexs
      *)

  End Translation.

End Forcing.

Declare ML Module "forcing_plugin".

