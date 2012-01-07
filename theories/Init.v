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

Section Forcing.
  Context {P:Type} `{C : Condition P}.

  Local Open Scope forcing_scope.

  Definition subp (p : P) := { q : P | q <= p }.

  (** [subp] also forms valid forcing conditions *)

  Program Instance subp_cond p : Condition (subp p) := 
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
  Proof. exists (` s). rewrite <- ι_inj. apply (proj2_sig s). Defined. (* apply (@ι (` (ι r)) (ι_lift r)). exists (`s). unfold ι_lift. simpl in *. apply (proj2_sig s).*) 

(*   Lemma ι_ι_ι {p} {q : subp p} {r : subp (` q)} (s : subp (` r)) :  *)
(*     ι (ι_ι s) = ι_ι (ι s). *)

  Program Lemma ι_refl {p} (q : subp p) : subp (` q).
  Proof. intros. exists (` q). reflexivity. Defined.

  Lemma ι_ι_refl {p} (q : subp p) : ι (ι_refl q) = q.
  Proof. unfold ι, ι_refl. simpl. destruct q. simpl. f_equal. apply le_pi. Defined.

  Hint Extern 0 (_ = _) => apply ι_ι_refl : forcing.

  Hint Extern 0 (_ <= _) => apply reflexivity : forcing. 
  Ltac prog_forcing := auto with forcing.
  Hint Extern 0 (_ = _) => try f_equal ; apply le_pi : forcing.

  Obligation Tactic := program_simpl ; prog_forcing.

  Section Translation.

    Definition transport {p} (f : subp p → Type) :=
      forall q : subp p, forall r : subp (` q), arrow (f q) (f (ι r)).

    Section Sheaf.
      Context {p} {f : subp p -> Type}.

      Notation " 'rewrite' p 'in' x " := (eq_rect _ _ x _ p) (at level 10).
      Set Transparent Obligations.

      Program Definition refl (Θ : transport f) :=
        forall q : subp p, forall x : f q, 
          (rewrite (ι_ι_refl q) in (Θ q (ι_refl q) x)) = x.
      
      Program Definition trans (Θ : transport f) := 
        forall q : subp p, forall r : subp q, forall s : subp r,
          (Θ (ι r) (ι_ι s)) ∘ (Θ q r) = Θ q (ι s).
    
      Next Obligation. unfold ι, ι_ι. simpl. f_equal. apply le_pi. Defined.

    End Sheaf.

    Record sheaf (p : P) :=
      { sheaf_f : subp p → Type ; 
        Θ : transport sheaf_f ;
        sheaf_refl : refl Θ ;
        sheaf_trans : trans Θ }.
        
    Set Hide Obligations.
    Obligation Tactic := idtac.

      Program Definition sheafC (p : P) (q : subp p) (r : subp (` q)) 
      (f : sheaf (` q)) : sheaf (` r) :=
      {| sheaf_f s := sheaf_f _ f (ι s) ;
         Θ := λ s : subp (`r), λ t : subp (` s), λ x : sheaf_f (` q) f (ι s),
         ((Θ (`q) f (ι s) (ι_ι t) x) : sheaf_f (`q) f (ι t))
        |}.

    Next Obligation. intros. unfold ι. f_equal. apply le_pi. Defined.

    Lemma eq_trans_eq_refl_l {A} (x y : A) (p : x = y) : eq_trans eq_refl p = p.
    Proof. destruct p. reflexivity. Defined.

    Lemma eq_trans_eq_refl_r {A} (x y : A) (p : x = y) : eq_trans p eq_refl = p.
    Proof. destruct p. reflexivity. Defined.

    Next Obligation. intros. 
      red. intros.
      set(foo:=ι_ι_refl q0).
      abstract_eq_proofs.
      unfold ι_refl in eqH. unfold ι in eqH.
      simpl in eqH. unfold ι_ι. unfold ι_refl. simpl. unfold ι; simpl. 
      destruct q0. simpl. destruct r. simpl. simpl in *.
      clearbody foo. unfold ι, ι_refl in *. simpl in *.
      erewrite eq_rect_irrel; [reflexivity|].
      destruct q. simpl in *. clear. abstract_eq_proofs.
    Admitted.

    Next Obligation.
 
Declare ML Module "forcing_plugin".

