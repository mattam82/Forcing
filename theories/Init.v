Require Export Unicode.Utf8_core.
Require Export Coq.Program.Program.
Require Import Relations RelationClasses Setoid.

Implicit Arguments projT1 [[A] [P]].
Implicit Arguments projT2 [[A] [P]].
Implicit Arguments existT [[A] [P]].

Definition prodT (A B : Type) := @sigT A (fun _ => B). 
Definition pairT {A B : Type} : A -> B -> prodT A B := @existT A (fun _ => B). 

Inductive prop_eq (P : Prop) (p : P) : P -> Prop := 
  prop_eq_refl : prop_eq P p p.

Implicit Arguments pairT [[A] [B]].

Definition conv_annot {T U : Type} (M : U) : U := M.
Definition app_annot {T} {U : T -> Type} {N : T} (V : U N) : U N := V.
  
Lemma equal_existT {A} {P : A -> Type} {p : A} {x y : P p} : x = y -> (existT p x = existT p y).
Proof. now intros ->. Defined.

Implicit Arguments exist [[A] [P]].

Lemma equal_exist {A} {P : A -> Prop} {p : A} {x y : P p} : exist p x = exist p y.
Proof. now intros. Defined.

Lemma exist_eq {A : Type} {P : A -> Prop} (x y : A) (p : P x) (q : P y) :
  x = y -> exist x p = exist y q.
Proof. intros; subst; reflexivity. Qed.

Lemma equal_f {A B : Type} {f g : A -> B} : f = g -> forall x : A, f x = g x. 
Proof. now intros ->. Qed.

Lemma equal_dep_f {A} {B : A -> Type} {f g : ∀ x : A, B x} : f = g -> forall x : A, f x = g x. 
Proof. now intros ->. Qed.

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

Notation " '{Σ' x , y } " := (exist x y).
Notation " '(Σ' x , y ) " := (existT x y).

(** Basic definitions for forcing *)

(** Forcing conditions come with a preorder *)

Module Type Condition. 
  Parameter P : Type.
  Parameter le : relation P.
  Declare Instance le_pre : PreOrder le.

  Delimit Scope forcing_scope with forcing.
  Notation " x <= y " := (le x y) : forcing_scope.

End Condition.

Inductive prop_or_type := is_prop | is_type.

Class ForcingOp {A : Type} (a : A) (p : prop_or_type) := {
  forcing_traduction_type : Type;
  forcing_traduction : forcing_traduction_type
}.

Implicit Arguments forcing_traduction [[A] [ForcingOp]].

Class ForcingLemma {P : Prop} (p : P) := {
  forcing_traduction_prop : Prop;
  forcing_traduction_proof : forcing_traduction_prop
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

  Program Definition embed (p : P) : subp p := p.
  Next Obligation. red; reflexivity. Qed.

  (** We define an overloaded [ι] operator to infer canonical 
     coercions of conditions into larger subsets. *)
  
  Class Iota p (x : subp p) q := { iota : subp q ;
    iota_identity : @eq P x iota
  }.
  
  Global Implicit Arguments iota [[p] [q] [Iota]].

  Notation ι r := (iota r).

  (*Hint Extern 4 => progress (unfold le in * ) : forcing.*)
  
  Lemma subp_proof2 p (q : subp p) : ` q <= p. 
  Proof. apply subp_proof. Defined.
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
                      (try (not_tried (iota_trans p q) ;
                            let foo := fresh "tried" in
                              set(foo:=Build_Tried (iota_trans p q)) ;
                            eapply iota_compose))). 

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
  Proof. exact (iota u). Defined.

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

    Lemma sheafC_trans (p : P) : trans_prop (sheafC p).
    Proof.
      red. split; red; intros.
      (* BUG with reflexivity only: eta for records probably *)
      destruct x as [sh [tr Htr]]; simpl. unfold sheafC. simpl. 
      unfold Θ. simpl. reflexivity.
      destruct x as [sh [tr Htr]]; simpl. unfold compose, sheafC. simpl. apply f_equal.
      unfold Θ. simpl. reflexivity.
    Qed.

    Program Definition sheafC_sheaf (p : P) :
              { sheaf_f : subp p -> Type & sig (@trans_prop p sheaf_f) } :=
              existT sheaf (exist (sheafC p) (sheafC_trans p)).

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

    Program Definition prop_sheafC_sheaf (p : P) :
              { sheaf_f : subp p -> Type & sig (@trans_prop p sheaf_f) } :=
              existT prop_sheaf (prop_sheafC p). 
    Next Obligation.
      red. split; red; intros.
      destruct x as [sh tr]; simpl. unfold prop_sheafC. simpl. reflexivity. 
      destruct x as [sh tr]; simpl. unfold compose, prop_sheafC. simpl. 
      reflexivity.
    Qed.

  End TranslationProp.

End Forcing.

Module NatForcing := Forcing(NatCondition).

Declare ML Module "forcing_plugin".

