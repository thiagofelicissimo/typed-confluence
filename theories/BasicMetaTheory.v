
From Stdlib Require Import Utf8 List Arith Bool Lia.
From TypedConfluence.autosubst
Require Import core unscoped AST SubstNotations RAsimpl AST_rasimpl.
From TypedConfluence Require Import Util BasicAST Weakenings Contexts Typing. (*  Env Inst. *)
From Stdlib Require Import Setoid Morphisms Relation_Definitions.


(*
  To prove the following properties, we can try to follow the same order as in 
  Harper & Pfenning's "On equivalence and canonical forms in the lf type theory".
  In any case, there is no doubt that they can be proven.
*)

Theorem refl_ty : forall Γ l t A, Γ ⊢< l > t : A -> Γ ⊢< l > t ≡ t : A.
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

Theorem validity_conv : forall Γ l t u A, Γ ⊢< l > t ≡ u : A -> (Γ ⊢< l > t : A) /\ (Γ ⊢< l > u : A).
Admitted.

Theorem type_unicity : forall Γ l l' t A B, Γ ⊢< l > t : A ->  Γ ⊢< l' > t : B -> (l = l') /\ (Γ ⊢< Ax l > A ≡ B : Sort l).
Admitted. 