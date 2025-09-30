
From Stdlib Require Import Utf8 List Arith Bool Lia.
From TypedConfluence.autosubst
Require Import core unscoped AST SubstNotations RAsimpl AST_rasimpl.
From TypedConfluence Require Import Util BasicAST Weakenings Contexts Typing. (*  Env Inst. *)
From Stdlib Require Import Setoid Morphisms Relation_Definitions.
Require Import Stdlib.Program.Equality.

Import ListNotations.
Import CombineNotations.

Open Scope subst_scope.


(*
  To prove the following properties, we can try to follow the same order as in 
  Harper & Pfenning's "On equivalence and canonical forms in the lf type theory".
  In any case, there is no doubt that they can be proven.
*)

Lemma type_inv_pi Γ l' i j A B T: 
  Γ ⊢< l' > Pi i j A B : T -> 
  Γ ⊢< Ax i > A : Sort i /\ Γ ,, (i, A) ⊢< Ax j > B : Sort j.
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

Theorem refl_ty : forall Γ l t A, Γ ⊢< l > t : A -> Γ ⊢< l > t ≡ t : A.
Admitted.


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

Corollary subst_ty : forall Γ l t u l' Δ σ, Δ ⊢s σ : Γ -> Γ ⊢< l > t ≡ u : Sort l' -> Δ ⊢< l > t <[ σ ] ≡ u <[ σ ] : Sort l'.
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

Theorem type_unicity : forall Γ l l' t A B, Γ ⊢< l > t : A ->  Γ ⊢< l' > t : B -> (l = l') /\ (Γ ⊢< Ax l > A ≡ B : Sort l).
Admitted. 