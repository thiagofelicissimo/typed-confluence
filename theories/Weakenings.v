
From Stdlib Require Import Utf8 List Arith Bool.
From TypedConfluence.autosubst
Require Import core unscoped AST SubstNotations RAsimpl AST_rasimpl.
From TypedConfluence Require Import Util BasicAST Contexts. (*  Env Inst. *)
From Stdlib Require Import Setoid Morphisms Relation_Definitions.


Import ListNotations.
Import CombineNotations.

Set Default Goal Selector "!".

Open Scope subst_scope.

Inductive wk : Set :=
  | _wk_id : wk
  | _wk_step (w : wk) : wk
  | _wk_up (w : wk) : wk.


(** Transforms an (intentional) weakening into a renaming. *)
Fixpoint wk_to_ren (ρ : wk) : nat -> nat :=
  match ρ with
    | _wk_id => id
    | _wk_step ρ' => (wk_to_ren ρ') >> S
    | _wk_up ρ' => up_ren (wk_to_ren ρ')
  end.


Definition wk_tm (ρ : wk) (t : term) : term := ren_term (wk_to_ren ρ) t.

Reserved Notation "t ⟨ ρ ⟩" (at level 50, ρ at next level).

Notation "t ⟨ ρ ⟩" := (wk_tm ρ t).

Inductive well_weakening : wk -> ctx -> ctx -> Prop :=
  | well_empty Δ : well_weakening _wk_id Δ Δ
  | well_step {Γ Δ : ctx} (A : term) (ρ : wk) l :
    well_weakening ρ Γ Δ -> well_weakening (_wk_step ρ) Γ (Δ ,, (l , A))
  | well_up {Γ Δ : ctx} (A : term) (ρ : wk) l :
    well_weakening ρ Γ Δ -> well_weakening (_wk_up ρ) (Γ,, (l , A)) (Δ ,, (l , wk_tm ρ A )).

Reserved Notation "ρ : Γ ⊆ Δ" (at level 50, Γ, Δ at next level).

(* OBS: I like have my weakening inclusions in the right direction ;) *)    
Notation "ρ : Γ ⊆ Δ" := (well_weakening ρ Γ Δ).