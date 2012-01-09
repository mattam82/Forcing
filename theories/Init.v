Require Export Unicode.Utf8_core.
Require Export Coq.Program.Program.
Require Import Relations.
Require Import RelationClasses.

(** Basic definitions for forcing *)

(** Forcing conditions come with a preorder *)

Class Condition (A : Type) := {
  le : relation A ;
  le_pre :> PreOrder le ;
  le_pi : forall x y (p q : le x y), p = q
}.

Delimit Scope forcing_scope with forcing.

Notation " x <= y " := (le x y) : forcing_scope.

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

    Record sheaf (p : P) :=
      { sheaf_f : subp p → Type ; 
        Θ : transport sheaf_f ;
        sheaf_refl : refl Θ ;
        sheaf_trans : trans Θ }.
        
(*     Obligation Tactic := idtac. *)

    Program Definition sheafC (p : P) (q : subp p) (r : subp (` q)) 
      (f : sheaf (` q)) : sheaf (` r) :=
      {| sheaf_f s := sheaf_f _ f (ι s) ;
        Θ := λ s : subp (`r), λ t : subp (` s), λ x : sheaf_f (` q) f (ι s),
          (Θ (`q) f (ι s) (ι_ι t) x) : sheaf_f (`q) f (ι_ι t)
        |}.

    Next Obligation. intros. unfold ι, ι_ι; simpl. f_equal. apply le_pi. Defined.

    Notation " '(Σ' x , y ) " := (exist _ x y).

    Next Obligation. intros. 
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
      set (foo := ((Θ0 (Σx0, ll0) ((exist (fun x => x <= x0) x0 (reflexivity x0)) : subp x0) x))).
      intros. unfold ι in foo. simpl in *.
      red in sheaf_refl0. specialize (sheaf_refl0 (Σx0, ll0) x). rewrite <- sheaf_refl0.
      unfold ι, ι_refl. simpl. rewrite eq_trans_eq_refl_l.
      rewrite eq_rect_f_equal. f_equal. pi.
    Qed.
    
    Next Obligation.
    Proof. intros.
      pose (sheaf_trans _ f).
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

  End Translation.

End Forcing.

Declare ML Module "forcing_plugin".

