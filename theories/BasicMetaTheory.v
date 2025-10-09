
From Stdlib Require Import Utf8 List Arith Bool Lia.
From TypedConfluence.autosubst
Require Import core unscoped AST SubstNotations RAsimpl AST_rasimpl.
From TypedConfluence Require Import Util BasicAST Weakenings Contexts Typing. (*  Env Inst. *)
From Stdlib Require Import Setoid Morphisms Relation_Definitions.
Require Import Stdlib.Program.Equality.

Import ListNotations.
Import CombineNotations.

Open Scope subst_scope.

Lemma Ax_inj l l' : Ax l = Ax l' -> l = l'.
Proof. 
  intro H. destruct l; destruct l'; inversion H; auto.
Qed.

(* basic inversion lemmas *)


Lemma type_inv_var Γ l x T : 
  Γ ⊢< l > var x : T -> 
  exists A, nth_error Γ x = Some (l , A).
Proof.
  intro H.
  dependent induction H; eauto.
Qed.

Lemma type_inv_pi Γ l' i j A B T: 
  Γ ⊢< l' > Pi i j A B : T -> 
  Γ ⊢< Ax i > A : Sort i /\ Γ ,, (i, A) ⊢< Ax j > B : Sort j.
Proof.
  intro H.
  dependent induction H; eauto.
Qed.

Lemma type_inv_lam Γ i j A B t T l :
      Γ ⊢< l > lam i j A B t : T ->
      Γ ⊢< Ax i > A : Sort i /\
      Γ ,, (i , A) ⊢< Ax j > B : Sort j /\
      Γ ,, (i , A) ⊢< j > t : B.
Proof.
  intro H.
  dependent induction H; eauto.
Qed.

Lemma type_inv_app Γ i j A B t u l T :
      Γ ⊢< l > app i j A B  t u : T ->
      Γ ⊢< Ax i > A : Sort i /\
      Γ ,, (i , A) ⊢< Ax j > B : Sort j /\
      Γ ⊢< Ru i j > t : Pi i j A B /\
      Γ ⊢< i > u : A.
Proof.
  intro H.
  dependent induction H; eauto.
Qed.

Lemma type_inv_succ Γ t T l :
      Γ ⊢< l > succ t : T ->
      Γ ⊢< ty 0 > t : Nat. 
Proof.
  intro H.
  dependent induction H; eauto.
Qed.

Lemma type_inv_rec Γ l' l P p_zero p_succ t T : 
  Γ ⊢< l' > rec l P p_zero p_succ t : T -> 
  Γ ,, (ty 0 , Nat) ⊢< Ax l > P : Sort l /\
  Γ ⊢< l > p_zero : P <[ zero .. ] /\
  Γ ,, (ty 0 , Nat) ,, (l , P) ⊢< l > p_succ : P <[ (succ (var 1)) .: (shift >> (shift >> var)) ] /\
  Γ ⊢< ty 0 > t : Nat.
Proof.
  intro H.
  dependent induction H; eauto.
Qed.

Lemma type_inv_box Γ T l :
      Γ ⊢< l > box : T ->
      False. 
Proof.
  intro H.
  dependent induction H; eauto.
Qed.


(*
  To prove the following properties, we can try to follow the same order as in 
  Harper & Pfenning's "On equivalence and canonical forms in the lf type theory".
  In any case, there is no doubt that they can be proven.
*)


Theorem refl_ty Γ l t A : Γ ⊢< l > t : A -> Γ ⊢< l > t ≡ t : A.
Proof.
  intros Wt.
  induction Wt; eauto using conversion.
Qed.



Theorem refl_subst : forall Γ σ Δ, Γ ⊢s σ : Δ -> Γ ⊢s σ ≡ σ : Δ.
Admitted.

Theorem subst_id : forall Γ, ⊢ Γ -> Γ ⊢s var : Γ.
Admitted.


Theorem refl_ctx : forall Γ, ⊢ Γ -> ⊢ Γ ≡ Γ.
Admitted.

Theorem wk_ty : forall Γ Δ l t A ρ, ⊢ Δ -> Γ ⊢< l > t : A -> ρ : Γ ⊆ Δ -> Δ ⊢< l > (wk_tm ρ t) : (wk_tm ρ A). (* why t ⟨ ρ ⟩ doesnt work ? *)
Admitted.

Theorem wk_conv : forall Γ Δ l t u A ρ, ⊢ Δ -> Γ ⊢< l > t ≡ u : A -> ρ : Γ ⊆ Δ -> Δ ⊢< l > (wk_tm ρ t) ≡ (wk_tm ρ u) : (wk_tm ρ A).
Admitted.

Theorem subst : forall Γ l t u A Δ σ τ, Δ ⊢s σ ≡ τ : Γ -> Γ ⊢< l > t ≡ u : A -> Δ ⊢< l > t <[ σ ] ≡ u <[ τ ] : A <[ σ ].
Admitted.


Theorem subst2 : forall Γ l t A Δ σ, Δ ⊢s σ : Γ -> Γ ⊢< l > t : A -> Δ ⊢< l > t <[ σ ] : A <[ σ ].
Admitted.


Corollary subst_ty : forall Γ l t u l' Δ σ, Δ ⊢s σ : Γ -> Γ ⊢< l > t ≡ u : Sort l' -> Δ ⊢< l > t <[ σ ] ≡ u <[ σ ] : Sort l'.
Admitted.


Corollary subst_ty' : forall Γ l t l' Δ σ, Δ ⊢s σ : Γ -> Γ ⊢< l > t : Sort l' -> Δ ⊢< l > t <[ σ ] : Sort l'.
Admitted.


Theorem conv_in_ctx_ty : forall Γ Δ l t A, ⊢ Γ ≡ Δ -> Γ ⊢< l > t : A -> Δ ⊢< l > t : A.
Admitted.

Theorem conv_in_ctx_conv : forall Γ Δ l t u A, ⊢ Γ ≡ Δ -> Γ ⊢< l > t ≡ u : A -> Δ ⊢< l > t ≡ u : A.
Admitted.

Theorem validity_ty : forall Γ l t A, Γ ⊢< l > t : A -> (⊢ Γ) /\ (Γ ⊢< Ax l > A : Sort l).
Admitted.

Theorem validity_ty_ctx : forall Γ l t A, Γ ⊢< l > t : A -> ⊢ Γ.
Admitted.

Theorem validity_ty_ty : forall Γ l t A, Γ ⊢< l > t : A -> Γ ⊢< Ax l > A : Sort l.
Admitted.

Theorem validity_conv : forall Γ l t u A, Γ ⊢< l > t ≡ u : A -> (Γ ⊢< l > t : A) /\ (Γ ⊢< l > u : A).
Admitted.

Theorem validity_conv_left : forall Γ l t u A, Γ ⊢< l > t ≡ u : A -> Γ ⊢< l > t : A.
Admitted.


Theorem validity_conv_right : forall Γ l t u A, Γ ⊢< l > t ≡ u : A -> Γ ⊢< l > u : A.
Admitted.

Theorem type_unicity : forall Γ l l' t A B, Γ ⊢< l > t : A ->  Γ ⊢< l' > t : B -> Γ ⊢< Ax l > A ≡ B : Sort l.
Admitted. 

Theorem sort_unicity : forall Γ l l' t A B, Γ ⊢< l > t : A ->  Γ ⊢< l' > t : B -> l = l'.
Admitted. 

Lemma validity_ctx_left Γ Δ : ⊢ Γ ≡ Δ -> ⊢ Γ.
Admitted.


Lemma conv_ctx_var Γ x l A Δ :
    nth_error Γ x = Some (l, A) -> 
    ⊢ Γ ≡ Δ -> 
    exists B, nth_error Δ x = Some (l, B) /\ Γ ⊢< Ax l > Init.Nat.add (S x) ⋅ A ≡ Init.Nat.add (S x) ⋅ B : Sort l.
Proof.
    intros. generalize l x A H. clear l x A H.
    induction H0; intros.
    - destruct x; inversion H.
    - destruct x. 
        + simpl in H. dependent destruction H. exists B. split. auto. admit. (* by weakening *)
        + simpl in H. apply IHConvCtx in H as (B0 & nth_x & conv). 
          exists B0. split; auto. admit. (* by weakening *)
Admitted.


(* composite lemmas, for helping automation *)

Lemma conv_ty_in_ctx_conv Γ l A A' l' t u B : 
  Γ ,, (l , A) ⊢< l' > t ≡ u : B ->
  Γ ⊢< Ax l > A ≡ A' : Sort l -> 
  Γ ,, (l , A') ⊢< l' > t ≡ u : B.
Proof.
  intros t_eq_u A_eq_A'.
  eapply conv_in_ctx_conv; eauto.
  apply conv_ccons; eauto using refl_ctx, validity_ty_ctx, validity_conv_left.
Qed.


Lemma conv_ty_in_ctx_ty Γ l A A' l' t B : 
  Γ ,, (l , A) ⊢< l' > t : B ->
  Γ ⊢< Ax l > A ≡ A' : Sort l -> 
  Γ ,, (l , A') ⊢< l' > t : B.
Proof.
  intros t_eq_u A_eq_A'.
  eapply conv_in_ctx_ty; eauto.
  apply conv_ccons; eauto using refl_ctx, validity_ty_ctx, validity_conv_left.
Qed.


Lemma aux_subst_1 Γ l t A :
  Γ ⊢< l > t : A ->
  Γ ⊢s t .. : (Γ ,, (l, A)).
Proof.
  intro kWt.
  apply well_scons; ssimpl; eauto using validity_ty_ctx, subst_id.
Qed.

(* the following lemma helps automation to type some substitutions that appear often in the proof *)
Lemma aux_subst_2 Γ l P : 
  Γ ,, (ty 0, Nat) ⊢< Ax l > P : Sort l ->
  (Γ,, (ty 0, Nat)),, (l, P) ⊢s (succ (var 1) .: ↑ >> (↑ >> var)) : Γ ,, (ty 0, Nat).
Proof.
  intro H.
  apply well_scons.
  - ssimpl. admit. (* by weakening *)
  - ssimpl. apply type_succ. apply (type_var _ 1 _ Nat); eauto. eauto using validity_ty_ctx, ctx_cons.
Admitted.


(* newer versions of inversion lemmas.
   TODO: replace in Confluence.v the occurrences of older inversion lemmas by the newer ones *)

Lemma type_inv_var' Γ l x T : 
  Γ ⊢< l > var x : T -> 
  Γ ⊢< l > var x : T /\ exists A, nth_error Γ x = Some (l , A) /\ Γ ⊢< Ax l > T ≡ (plus (S x)) ⋅ A : Sort l.
Proof.
  intro H.
  apply validity_ty_ty in H as T_Wt.
  split. auto.
  dependent induction H.
  - eexists. split; eauto using refl_ty.
  - edestruct IHtyping as (C & eq & A_eq_C); eauto using validity_conv_left. eexists. split; eauto using conv_trans, conv_sym.
Qed.

Lemma type_inv_sort' Γ l' i T: 
  Γ ⊢< l' > Sort i : T -> 
  Γ ⊢< l' > Sort i : T /\ 
  l' = Ax (Ax i) /\ 
  Γ ⊢< Ax (Ax (Ax i)) > T ≡ Sort (Ax i) : Sort (Ax (Ax i)).
Proof.
  intro H.
  apply validity_ty_ty in H as T_Wt.
  split. auto.
  dependent induction H.
  - repeat split; eauto using refl_ty.
  - edestruct IHtyping as (l_eq & conv); eauto using validity_conv_left.
    rewrite l_eq in *. repeat split; eauto using conv_trans, conv_sym.
Qed.

Lemma type_inv_pi' Γ l' i j A B T: 
  Γ ⊢< l' > Pi i j A B : T -> 
  Γ ⊢< l' > Pi i j A B : T /\ 
  Γ ⊢< Ax i > A : Sort i /\ 
  Γ ,, (i, A) ⊢< Ax j > B : Sort j /\ 
  l' = Ax (Ru i j) /\ 
  Γ ⊢< Ax (Ax (Ru i j)) > T ≡ Sort (Ru i j) : Sort (Ax (Ru i j)).
Proof.
  intro H.
  apply validity_ty_ty in H as T_Wt.
  split. auto.
  dependent induction H.
  - repeat split; eauto using refl_ty.
  - edestruct IHtyping as (AWt & BWt & l_eq & conv); eauto using validity_conv_left.
    rewrite l_eq in *. repeat split; eauto using conv_trans, conv_sym.
Qed.

Lemma type_inv_lam' Γ i j A B t T l :
      Γ ⊢< l > lam i j A B t : T ->
      Γ ⊢< l > lam i j A B t : T /\
      Γ ⊢< Ax i > A : Sort i /\
      Γ ,, (i , A) ⊢< Ax j > B : Sort j /\
      Γ ,, (i , A) ⊢< j > t : B /\ 
      l = Ru i j /\
      Γ ⊢< Ax (Ru i j) > T ≡ Pi i j A B : Sort (Ru i j).
Proof.
  intro H.
  apply validity_ty_ty in H as T_Wt.
  split. auto.
  dependent induction H; eauto.
  - repeat split; eauto using refl_ty.
  - edestruct IHtyping as (AWt & BWt & tWt & l_eq & conv); eauto using validity_conv_left.
    rewrite l_eq in *. repeat split; eauto using conv_trans, conv_sym.
Qed.

Lemma type_inv_app' Γ i j A B t u l T :
      Γ ⊢< l > app i j A B t u : T ->
      Γ ⊢< l > app i j A B t u : T /\
      Γ ⊢< Ax i > A : Sort i /\
      Γ ,, (i , A) ⊢< Ax j > B : Sort j /\
      Γ ⊢< Ru i j > t : Pi i j A B /\
      Γ ⊢< i > u : A /\ 
      l = j /\ 
      Γ ⊢< Ax j > T ≡ B <[ u.. ] : Sort j.
Proof.
  intro H.
  apply validity_ty_ty in H as T_Wt.
  split. auto.
  dependent induction H; eauto.
  - repeat split; eauto using refl_ty.
  - edestruct IHtyping as (AWt & BWt & tWt & uWt & l_eq & conv); eauto using validity_conv_left.
    rewrite l_eq in *. repeat split; eauto using conv_trans, conv_sym.
Qed.

Lemma type_inv_nat' Γ l' T: 
  Γ ⊢< l' > Nat : T -> 
  Γ ⊢< l' > Nat : T /\ 
  l' = ty 1 /\ 
  Γ ⊢< ty 2 > T ≡ Sort (ty 0) : Sort (ty 1).
Proof.
  intro H.
  apply validity_ty_ty in H as T_Wt.
  split. auto.
  dependent induction H.
  - repeat split; eauto using refl_ty.
  - edestruct IHtyping as (l_eq & conv); eauto using validity_conv_left.
    rewrite l_eq in *. repeat split; eauto using conv_trans, conv_sym.
Qed.


Lemma type_inv_zero' Γ l' T: 
  Γ ⊢< l' > zero : T -> 
  Γ ⊢< l' > zero : T /\ 
  l' = ty 0 /\ 
  Γ ⊢< ty 1 > T ≡ Nat : Sort (ty 0).
Proof.
  intro H.
  apply validity_ty_ty in H as T_Wt.
  split. auto.
  dependent induction H.
  - repeat split; eauto using refl_ty.
  - edestruct IHtyping as (l_eq & conv); eauto using validity_conv_left.
    rewrite l_eq in *. repeat split; eauto using conv_trans, conv_sym.
Qed.


Lemma type_inv_succ' Γ t T l :
      Γ ⊢< l > succ t : T ->
      Γ ⊢< l > succ t : T /\
      Γ ⊢< ty 0 > t : Nat /\ 
      l = ty 0 /\ 
      Γ ⊢< ty 1 > T ≡ Nat : Sort (ty 0).
Proof.
  intro H.
  apply validity_ty_ty in H as T_Wt.
  split. auto.
  dependent induction H; eauto.
  - repeat split; eauto using refl_ty.
  - edestruct IHtyping as (tWt & l_eq & conv); eauto using validity_conv_left.
    rewrite l_eq in *. repeat split; eauto using conv_trans, conv_sym.
Qed.

Lemma type_inv_rec' Γ l' l P p_zero p_succ t T : 
  Γ ⊢< l' > rec l P p_zero p_succ t : T -> 
  Γ ⊢< l' > rec l P p_zero p_succ t : T /\
  Γ ,, (ty 0 , Nat) ⊢< Ax l > P : Sort l /\
  Γ ⊢< l > p_zero : P <[ zero .. ] /\
  Γ ,, (ty 0 , Nat) ,, (l , P) ⊢< l > p_succ : P <[ (succ (var 1)) .: (shift >> (shift >> var)) ] /\
  Γ ⊢< ty 0 > t : Nat /\ 
  l' = l /\ 
  Γ ⊢< Ax l > T ≡ P <[ t.. ] : Sort l.
Proof.
  intro H.
  apply validity_ty_ty in H as T_Wt.
  split. auto.
  dependent induction H; eauto.
  - repeat split; eauto using refl_ty.
  - edestruct IHtyping as (PWt & p_zeroWt & p_succWt & tWt & l_eq & conv); eauto using validity_conv_left.
    rewrite l_eq in *. repeat split; eauto using conv_trans, conv_sym.
Qed.
