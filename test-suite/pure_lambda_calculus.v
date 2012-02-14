Require Import Setoid.
Require Import FunctionalExtensionality.
Set Implicit Arguments.

Require Export Unicode.Utf8_core.
Require Export Coq.Program.Program.
Require Import Relations RelationClasses Setoid.

Definition comp T U V (g:U->V) (f:T->U) := fun x => g (f x). 

Lemma eq_rect_sym {A} {Q : A -> Type} (x y : A) (p : Q y) (prf : x = y) :
  eq_rect x Q (eq_rect y Q p x (eq_sym prf)) y prf = p.
Proof. destruct prf. simpl. reflexivity. Qed.

Lemma eq_rect_comm {A} {Q : A -> Type} (x y : A) (p : Q y) (prf : x = y) (prf' : y = x) :
  eq_rect x Q (eq_rect y Q p x prf') y prf = p.
Proof. replace prf' with (eq_sym prf) by apply proof_irrelevance. apply eq_rect_sym. Qed.


Section later_operator.
    
  Parameter later : Type -> Type.

  Fixpoint nlater n T := match n with
                           | 0 => T
                           | S n' => later (nlater n' T)
                         end.

  Parameter next : forall {T}, T -> later T.

  Parameter switch : later Type -> Type.
  
  Axiom switch_next : forall (T:Type), switch (next T) = later T.

  Parameter later_arrow : forall T U , later (T -> U) -> (later T -> later U).

  Parameter later_arrow' : forall T U , (later T -> later U) -> later (T -> U).

  (* proofs of the following two axioms should be eq_refl *)  

  Axiom later_arrow_comm : forall T U (f:later(T->U)), later_arrow' (later_arrow f) = f.
  Axiom later_arrow_comm' : forall T U (f:later T-> later U), later_arrow (later_arrow' f) = f.
  
  Definition next_arrow T U (f: T -> U) := later_arrow (next f).
  
  (* proofs of the following four axioms should be eq_refl *)
  
  Axiom next_naturality : forall T U (f:T -> U) (v:T), next (f v) = (next_arrow f) (next v).

  Axiom next_arrow_comp : forall T U V (g:U->V) (f:T->U) x, 
    next_arrow (comp g f) x = (next_arrow g) ((next_arrow f) x).

  Axiom next_arrow_id : forall T, next_arrow (id (A:=T)) = id (A:=later T).

  Axiom next_arrow_wird : forall T U V (M : forall {n}, nlater n T -> nlater n U -> nlater n V) n g, 
    later_arrow ((next_arrow M) (next g)) = M (n := S n) (next g).

  Lemma next_arrow_curry : forall T U V (f: T->U->V) v, 
    next_arrow (f v) = later_arrow (next_arrow f (next v)).
  Proof.
    intros; unfold next_arrow at 1; rewrite next_naturality.
    reflexivity.
  Qed.
  
  Lemma next_arrow_next : forall T U V (M : forall {n}, nlater n T -> nlater n U -> nlater n V) n g, 
    next_arrow (M g) = M (n := S n) (next g).
  Proof.
    intros.
    rewrite next_arrow_curry.
    rewrite next_arrow_wird.
    reflexivity.
  Qed.

End later_operator.

Section fixpoint.
  
  Parameter fix_gen : forall {T}, ((later T) -> T) -> T.

  Notation " '(Σ' x , y ) " := (exist _ x y).

  (* proof of the following axiom should be eq_refl *)

  Axiom eqfix : forall T {G} , fix_gen (T:=T) G = G (next (fix_gen G)).

  Definition fixG := fix_gen (T:=Type).

  Definition fix_fold {G} (t : fixG G) := eq_rect _ id t _ eqfix.
  
  Definition fix_unfold {G} (t : G(next (fixG G))) := eq_rect _ (id(A:=Type)) t _ (eq_sym eqfix).

  Variable F : Type -> Type.

  Definition mu (F : Type -> Type) := fixG (fun T => F (switch T)).

  Lemma eqmu : mu F = F (later (mu F)).
  Proof.
    rewrite <- switch_next.
    apply (eqfix (G := fun T => F (switch T))).
  Qed.

  Definition fold (t : mu F) : F (later (mu F)) := eq_rect _ (id (A:=Type)) t _ eqmu.

  Definition unfold (t : F(later (mu F))) : mu F := eq_rect _ (id(A:=Type)) t _ (eq_sym eqmu).

  Lemma pi : forall (t : mu F), unfold (fold t) = t.
  Proof.
    intros; unfold fold, unfold.
    rewrite eq_rect_comm; reflexivity.
  Qed.

  Lemma pi' : forall (t : F (later (mu F))), fold (unfold t) = t.
  Proof.
    intros; unfold fold, unfold.
    rewrite eq_rect_comm; reflexivity.
  Qed.

  
  (*********************************************************)
  (* Definition for a fixpoint for which later_F(') exists *)
  (*********************************************************)

  Variable later_F : forall T, later (F T) -> F (later T).
  Variable later_F' : forall T, F (later T) -> later (F T).
  
  Variable later_F_comm : forall T (x:later (F T)), later_F' (later_F x) = x.
  Variable later_F_comm' : forall T (x:F (later T)), later_F (later_F' x) = x.

  Fixpoint nfold {n} : nlater n (mu F) -> F (nlater (S n) (mu F)) :=
    match n with 
      | 0 => fun x => fold x
      | S n' => fun x => (later_F ((next_arrow nfold) x))
    end.

  Fixpoint nunfold {n} : F (nlater (S n) (mu F)) -> nlater n (mu F) := 
    match n with 
      | 0 => fun x => unfold x
      | S n' => fun x => ((next_arrow nunfold) (later_F' x))
    end.

  Lemma npi_aux : forall n, comp nunfold nfold = id (A:= nlater n (mu F)).
  Proof.
    induction n; apply functional_extensionality; unfold comp; simpl; intros.
    apply pi.
    rewrite later_F_comm.
    rewrite <- next_arrow_comp.
    setoid_rewrite IHn.
    rewrite next_arrow_id; reflexivity.
  Qed.

  Lemma npi : forall n (t:nlater n (mu F)), nunfold (nfold t) =  t.
  Proof.
    intros; assert (Haux := npi_aux n).
    eapply equal_f in Haux; apply Haux.
  Qed.
  
  Lemma npi'_aux : forall n, comp nfold nunfold = id (A:=F (nlater (S n) (mu F))).
  Proof.
    induction n; apply functional_extensionality; unfold comp; simpl; intros.
    apply pi'.
    rewrite <- next_arrow_comp.
    setoid_rewrite IHn.
    rewrite next_arrow_id.
    apply later_F_comm'.
  Qed.
  
  Lemma npi' : forall n (t:F (nlater (S n) (mu F))), nfold (nunfold t) =  t.
  Proof.
    intros; assert (Haux := npi'_aux n).
    eapply equal_f in Haux; apply Haux.
  Qed.

  Definition next_F T (f: F T) : F (later T) := later_F (next f).

  Lemma fold_next : forall n (f:nlater n (mu F)),
    nfold (n:=S n) (next f) = next_F (nfold f).
  Proof.
    simpl; intros; rewrite <- next_naturality; reflexivity.
  Qed.
    
  Lemma unfold_next : forall n (f: F (nlater (S n) (mu F))), 
    nunfold (n:=S n) (next_F f) = next (nunfold f).
  Proof.
    simpl; intros. 
    unfold next_F; rewrite later_F_comm.
    rewrite <- next_naturality; reflexivity.
  Qed.
 
End fixpoint.

Section pure_lambda_calculus.

  Definition F := fun T => T -> T.
  Definition D := mu F.

  (* specializing the theory of fixpoint for the pure lambda calculus *)

  Definition later_F := (fun T => later_arrow' (T:=T) (U:=T)).
  Definition later_F' := (fun T => later_arrow (T:=T) (U:=T)).
  Definition later_F_comm := (fun T => later_arrow_comm' (T:=T) (U:=T)).
  Definition later_F_comm' := (fun T => later_arrow_comm (T:=T) (U:=T)).

  Definition ffun {n} (t : F (nlater (S n) D)) := nunfold F later_F t.
  Definition defun {n} (t : nlater n D) := nfold F later_F' t.

  Definition piF := npi F later_F' later_F later_F_comm'.
  Definition piF' := npi' F later_F' later_F later_F_comm.

  Definition defun_next := fold_next F later_F'.
  Definition ffun_next := unfold_next F later_F' later_F later_F_comm'.

  (* Definitions specific to the pure lambda calculus *)
 
  Definition const_fun {n} (t:nlater n D) := fun _ : nlater n D => t.
  Definition lift {n} (t: nlater (S n) D) := ffun (fun x => const_fun t x).
  Definition one_step {n} (x:nlater n D) := lift (next x).
  
  Definition app {n} (f:nlater n D) (s:nlater n D) := lift ((defun f) (next s)).

  Lemma lift_next : forall n (f:nlater (S n) D), lift (n:=S n) (next f) = next (lift f).
  Proof.
    intros; unfold lift.
    rewrite <- ffun_next.
    (* Lemma foo3 : forall n (f: nlater (S n) D), *)
    (*   (fun x : nlater (S (S n)) D => const_fun (n := S (S n)) (next f) x) = next_arrow (const_fun f). *)
    (* Proof. *)
    (*   intros; apply functional_extensionality; intros. *)
    (*   unfold const_fun. *)
    rewrite <- next_arrow_next.
    reflexivity.
  Qed.

  Lemma app_next : forall n (f:nlater n D) v, 
    app (n:=S n) (next f) (next v) = next (app f v).
  Proof.
    intros.
    unfold app.
    rewrite <- lift_next.
    repeat rewrite defun_next.
    setoid_rewrite <- next_naturality.
    reflexivity.
  Qed.
  
  (* Definition of Omega and its reduction *)
  
  Definition Omega {n} := ffun (fun x => app (n:=S n) x x).
  
  Lemma Omega_step : forall n, app (n:=n) Omega Omega = one_step (app Omega Omega).
  Proof.
    intro n; unfold app at 1, Omega at 1.
    unfold defun, ffun. 
    rewrite piF'.
    rewrite app_next.
    reflexivity.
  Qed.

  (* Definition of Y and its reduction *)

  Definition Y_aux {n} f := fun x => app (n:=n) f (app x x).
  
  Definition Y' {n} f := ffun (fun x => Y_aux (n:=S (S n)) (next f) x).

  Definition Y {n} := ffun (fun f => app (n := S n) (Y' f) (Y' f)).

  Lemma Y_aux_next : forall n (g:nlater (S (S n)) D),
    ffun (fun x => Y_aux (n:=S(S(S n))) (next g) x) = next (ffun (Y_aux g)).
  Proof.
    intros; rewrite <- ffun_next.
    rewrite <- next_arrow_next.
    reflexivity.
  Qed.
  
  Lemma Y'_next : forall n (g:nlater (S n) D), app (Y' (n:=S n) (next g)) (Y' (n:=S n) (next g)) = next (app (Y' (n:=n) g) (Y' (n:=n) g)).
  Proof.
    intros; unfold Y'. 
    repeat rewrite <- app_next.
    setoid_rewrite <- (Y_aux_next (next g)).
    reflexivity.
  Qed.
  
  Lemma Y_step : forall n g , app (n:= S n) Y g = one_step (one_step (app g (app (Y' g) (Y' g)))). 
  Proof with repeat rewrite app_next.
    intros n g.
    unfold app at 1, Y at 1, defun at 1; rewrite piF'.
    unfold app at 1, Y' at 1, Y_aux at 1, defun at 1; rewrite piF'...
    rewrite lift_next.
    rewrite Y'_next...
    reflexivity.
  Qed.

End pure_lambda_calculus.





