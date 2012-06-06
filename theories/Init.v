Require Export Unicode.Utf8_core.
Require Export Coq.Program.Program.
Require Import Relations RelationClasses Setoid.

Implicit Arguments projT1 [[A] [P]].
Implicit Arguments projT2 [[A] [P]].
Implicit Arguments existT [[A] [P]].

Definition prodT (A B : Type) := @sigT A (fun _ => B). 
Definition pairT {A B : Type} : A -> B -> prodT A B := @existT A (fun _ => B). 

Implicit Arguments pairT [[A] [B]].

Definition conv_annot {T U : Type} (M : U) : U := M.
Definition app_annot {T} {U : T -> Type} {N : T} (V : U N) : U N := V.

Definition eq_type {A B : Type} (p : A = B) (a : A) (b : B) := 
  eq_rect _ (fun X => X) a _ p = b.

(* Eq_rect lemmas *)

Lemma eq_rect_irrel A (x : A) P (px : P x) y prf (py : P y) : 
  px = eq_rect y P py x (symmetry prf) -> eq_rect x P px y prf = py.
Proof.
  intros. destruct prf. simpl in *. exact H.
Qed.

Lemma eq_rect_f_equal {A B} (f : A -> B) (x y : A) (P : B -> Type) (p : P (f x)) (prf : x = y) :
  eq_rect (f x) P p (f y) (f_equal f prf) (* P (f y) *) =
  eq_rect x (fun x => P (f x)) p y prf.
Proof. destruct prf. simpl. reflexivity. Defined.

(* Lemma eq_trans_eq_refl_l {A} (x y : A) (p : x = y) : eq_trans eq_refl p = p. *)
(* Proof. destruct p. reflexivity. Defined. *)
  
(* Lemma eq_trans_eq_refl_r {A} (x y : A) (p : x = y) : eq_trans p eq_refl = p. *)
(* Proof. destruct p. reflexivity. Defined. *)

Lemma eq_rect_sym {A} {Q : A -> Type} (x y : A) (p : Q y) (prf : x = y) :
  eq_rect x Q (eq_rect y Q p x (eq_sym prf)) y prf = p.
Proof. destruct prf. simpl. reflexivity. Qed.

Lemma eq_rect_comm {A} {Q : A -> Type} (x y : A) (p : Q y) (prf : x = y) (prf' : y = x) :
  eq_rect x Q (eq_rect y Q p x prf') y prf = p.
Proof. change prf' with (eq_sym prf). apply eq_rect_sym. Qed.

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

Lemma equal_existT {A} {P : A -> Type} {p : A} {x y : P p} : x = y -> (existT p x = existT p y).
Proof. now intros ->. Defined.

Lemma simplification_existT2' A (P : A -> Type) (p : A) (x y : P p) 
  (B : forall H : (existT p x = existT p y), Type) :
  (forall H : x = y, B (equal_existT H)) -> (forall H : (existT p x = existT p y), B H).
Proof. intros H E. injection E. simplify_dep_elim. apply (H eq_refl). Defined.

Implicit Arguments exist [[A] [P]].

Lemma equal_exist {A} {P : A -> Prop} {p : A} {x y : P p} : exist p x = exist p y.
Proof. now intros. Defined.

Require Import EqdepFacts.

Lemma simplification_exist A (P : A -> Prop) (p : A) (x y : P p) 
  (B : forall H : (exist p x = exist p y), Type) :
  (B equal_exist) -> (forall H : _ = _, B H).
Proof. intros H E. apply H. Defined.

Lemma simplification_existP A (P : A -> Prop) (p : A) (x y : P p) 
  (B : forall H : (exist p x = exist p y), Prop) :
  (B equal_exist) -> (forall H : _ = _, B H).
Proof. intros H E. apply H. Defined.

Lemma eq_rect_exist {B} {R : B -> Prop} {Q : sig R -> Type} (b : B) (x y : R b) (p : Q (exist b x)) 
  (prf : exist b x = exist b y) :
  eq_rect (exist b x) Q p (exist b y) prf = (p : Q (exist b y)).
Proof. change prf with (@eq_refl _ (exist b x)). reflexivity. Qed.

Ltac simpl_eq_rect_exist :=
 match goal with
   |- context[ eq_rect (exist ?q ?H) ?P ?p (exist ?q ?H') ?prf ] => 
     rewrite (eq_rect_exist (Q:=P) q H H' p prf)
 end.

(* Lemma eq_rect_pi {A : Prop} {Q : A -> Type} (p q : A) (x : forall x : A, Q x) : *)
(*   eq_rect p Q (x p) q (proof_irrelevance A p q) = x q. *)
(* Proof. set(foo:=proof_irrelevance A p q). destruct foo. simpl. reflexivity. Qed. *)

(* To control backtracking during proof search *)
Class Tried (P : Prop).

Ltac not_tried p :=
  match goal with
    | [ H : Tried ?Q |- _ ] =>
      match Q with 
        p => fail 2
      end
    | _ => idtac
  end.


(** Basic definitions for forcing *)

(** Forcing conditions come with a preorder *)

Module Type Condition. 
  Parameter P : Type.
  Parameter le : relation P.
  Declare Instance le_pre : PreOrder le.

  Delimit Scope forcing_scope with forcing.
  Notation " x <= y " := (le x y) : forcing_scope.

End Condition.

Class ForcingOp {A : Type} (a : A) := {
  forcing_traduction_type : Type;
  forcing_traduction : forcing_traduction_type
}.

Require Import Le.
Module NatCondition <: Condition.
  Definition P := nat.

  Definition le := Peano.le.

  Instance le_pre : PreOrder le.
  Proof. split; red; intros. apply le_n. eapply le_trans; eauto. Qed.

  Delimit Scope forcing_scope with forcing.
  Notation " x <= y " := (le x y) : forcing_scope.

End NatCondition.

Module Forcing(F : Condition).
  Import F.

  Local Open Scope forcing_scope.

  Definition Psub (p : P) := fun q : P => q <= p.

  Definition subp (p : P) := sig (Psub p).

  Definition subp_proj {p : P} (q : subp p) : P := ` q.
  Global Coercion subp_proj : subp >-> P.

  Definition ssubp {p} (q : subp p) := subp (subp_proj q).

  (** [subp] also forms valid forcing conditions *)

  Program Definition subp_intro {p : P} (q : P) (prf : q <= p) : subp p := q.
  
  Lemma subp_proof {p} (q : subp p) : (subp_proj q) <= p.
  Proof. apply (proj2_sig q). Defined.
  Hint Resolve subp_proof : forcing.

  Program Definition iota_refl p : subp p := p.
  Next Obligation. red; reflexivity. Qed.

  (** We define an overloaded [ι] operator to infer canonical 
     coercions of conditions into larger subsets. *)
  
  Class Iota p (x : subp p) q := { iota : subp q ;
    iota_identity : @eq P x iota
  }.
  
  Global Implicit Arguments iota [[p] [q] [Iota]].

  
  Hint Extern 0 (_ <= _) => apply reflexivity : forcing. 
  Hint Extern 0 (_ = _) => try f_equal ; reflexivity : forcing.

  Ltac forcing := 
    try solve [simpl; unfold Psub in *; auto with arith forcing].
  Obligation Tactic := program_simpl; forcing.

  (** The identity, in case no coercion was needed in fact *)
  Global Program Instance iota_reflexive p (q : subp p) : Iota p q p := { iota := (q : P) }.
  
  (** Self-indexing [q : P p] then [q : P q] *)
  Global Program Instance iota_lift p (q : subp p) : Iota p q q := { iota := (q : P) }.
    
  (** [q : P p] so forall [r : P q] [r : P p] as well *)
  Global Program Instance iota_pi {p} (q : subp p) : Iota q (iota q) p := 
    { iota := (q : P) }.
      
  (** [q : P p] so forall [r : P q] [r : P p] as well *)
  Global Program Instance iota_pi_inv {p} (q : subp p) (r : subp q) : Iota q r p :=
    { iota := (r : P) }.

  Next Obligation. red; transitivity q; auto with forcing. Defined.

  (** Iotas compose *)
  Program Definition iota_compose {p sp q r} (pq : Iota p sp q) (qr : Iota q (iota sp) r) : Iota p sp r :=
    {| iota := iota (iota sp) |}.

  Next Obligation. now repeat rewrite <- iota_identity. Defined.

  (**  In case [iota] does not change the type, it's the identity *)
  Lemma iota_iota_refl {p} (q : subp p) : iota (iota q) = q.
  Proof. now destruct q. Qed.

  Lemma iota_irrel {p} (q : subp p) {r} (X Y : Iota p q r) : iota (Iota:=X) q = iota (Iota:=Y) q.
  Proof. destruct X, Y. unfold iota; simpl. destruct iota0, iota1. simpl in *. subst. reflexivity. Qed.

  CoInductive iota_trans : P -> P -> Prop := .

  (** [iota_compose] is always applicable, restrict it to cases where both [p] and [r] 
     are ground and check for loops. *)
  Ltac apply_iota_compose p sp q :=
    progress (is_evar p || is_evar q || 
      not_tried (iota_trans p q) ;
              let foo := fresh "tried" in
                set(foo:=Build_Tried (iota_trans p q)) ;
              eapply iota_compose). 

  Hint Extern 3 (Iota ?p ?sp ?q) => apply_iota_compose p sp q : typeclass_instances.

  Ltac test_iota_compose :=
    match goal with
      |- Iota ?p ?sp ?q => apply_iota_compose p sp q
    end.
  
  Goal forall p sp q r (iop : Iota p sp q), Iota q (iota sp) r -> Iota p sp r.
  Proof. intros. typeclasses eauto. Qed.

  Goal forall p sp q r, Iota p sp q -> Iota p sp r.
  Proof. intros. 
    Fail typeclasses eauto. admit. Qed.

  Example one_trans p (q : subp p) (r : subp q) (s : subp r) : subp q.
  Proof. exact (iota s). Defined.

  Example two_trans p (q : subp p) (r : subp q) (s : subp r) (t : subp s) : subp q.
  Proof. exact (iota t). Defined.

  Example three_trans p (q : subp p) (r : subp q) (s : subp r) (t : subp s) (u : subp t) : subp q.
  Proof. exact (iota u). Show Proof. Defined.

    (* Maybe use those instances more? *)
  Global Instance one_trans_inst p (q : subp p) (r : subp q) (s : subp r) : Iota _ s q := { iota := iota s }.
  Proof. reflexivity. Defined.

  Global Instance two_trans_inst p (q : subp p) (r : subp q) (s : subp r) (t : subp s) : Iota _ t q := { iota := iota t }.
  Proof. reflexivity. Defined.

  Global Instance three_trans_inst p (q : subp p) (r : subp q) (s : subp r) (t : subp s) (u : subp t) : Iota _ u q := {iota := iota u}.
  Proof. reflexivity. Defined.

  Example four_trans p (q : subp p) (r : subp q) (s : subp r) (t : subp s) (u : subp t) (v : subp u) 
  : subp q.
  Proof. exact (iota v). Defined.

  Section Translation.
    
    Definition transport {p} (f : subp p → Type) :=
      forall q : subp p, forall r : subp q, arrow (f q) (f (iota r)).

    Section Sheaf.
      Context {p} {f : subp p -> Type}.

      Notation " 'rewrite' p 'in' x " := (eq_rect _ _ x _ p) (at level 10).

      Definition refl (Θ : transport f) := Eval simpl in
        forall q : subp p, forall x : f q, 
          Θ q (iota q) x = x.
      
      Definition trans (Θ : transport f) := Eval simpl in
        forall q : subp p, forall r : subp q, forall s : subp r,
          forall x, ((Θ (iota r) s) ∘ (Θ q r)) x = Θ q (iota s) x.

      Definition trans_prop (Θ : transport f) := 
        refl Θ /\ trans Θ.

    End Sheaf.

    Definition sheaf (p : P) :=
      { sheaf_f : subp p -> Type & sig (@trans_prop p sheaf_f) }.

    Definition sheaf_f {p : P} (s : sheaf p) : subp p -> Type :=
      projT1 s.

    Program Definition Θ {p : P} (s : sheaf p) : transport (sheaf_f s) :=
      projT2 s.

    Definition sheaf_refl {p} (s : sheaf p) : refl (Θ s).
    Proof. unfold Θ. destruct s. destruct s. destruct t. simpl. assumption. Defined.

    Definition sheaf_trans {p} (s : sheaf p) : trans (Θ s).
    Proof. unfold Θ. destruct s. destruct s. destruct t. simpl. assumption. Defined.

    Program Definition sheafC (p : P) (q : subp p) (r : subp q) 
      (f : sheaf q) : sheaf r :=
        existT (fun s => sheaf_f f (iota s))
        (λ s : subp r, λ t : subp s, λ x : sheaf_f f (iota s),
          (Θ f (iota s) t x)). 

    Notation " '{Σ'  x } " := (exist x _).

    Next Obligation. split; red. intros. 
      simpl.
      destruct q0. simpl. 
      destruct f. simpl in *.
      destruct s as [θ [Hr Ht]]. 
      red in Hr. pose (Hr _ x). simpl in *.
      rewrite <- e at 2. unfold Θ. simpl. reflexivity.

      (* Trans *)
      pose proof (sheaf_trans f).
      intros. unfold compose. destruct f; simpl in *.
      destruct s0 as [θ [Hr Ht]]. 
      red in Ht. pose (Ht (iota q0) r0 s x). unfold compose in *. simpl in *.
      unfold Θ. simpl in *. rewrite <- e. destruct r0; reflexivity.
    Qed.

  End Translation.

  Section TranslationProp.
    
    Definition prop_transport {p} (f : subp p → Prop) :=
      forall q : subp p, forall r : subp q, f q -> f (iota r).

    Definition prop_sheaf (p : P) :=
      { sheaf_f : subp p -> Prop | prop_transport sheaf_f }.

    Definition prop_sheaf_f {p : P} (s : prop_sheaf p) : subp p -> Prop :=
      proj1_sig s.

    Program Definition prop_Θ {p : P} (s : prop_sheaf p) : prop_transport (prop_sheaf_f s) :=
      proj2_sig s.

    Program Definition prop_sheafC (p : P) (q : subp p) (r : subp q) 
      (f : prop_sheaf q) : prop_sheaf r :=
        exist (fun s => prop_sheaf_f f (iota s)) _.


    Next Obligation. red. intros. 
      destruct f.
      simpl in *.
      specialize (p0 _ (iota r0) H). apply p0.
    Qed.

  End TranslationProp.

End Forcing.

Module NatForcing := Forcing(NatCondition).

Declare ML Module "forcing_plugin".

