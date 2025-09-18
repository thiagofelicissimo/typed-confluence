

From Stdlib Require Import Utf8 List Arith Bool.
From TypedConfluence.autosubst
Require Import core unscoped AST SubstNotations RAsimpl AST_rasimpl.
From TypedConfluence Require Import Util BasicAST. (*  Env Inst. *)
From Stdlib Require Import Setoid Morphisms Relation_Definitions.

Import ListNotations.
Import CombineNotations.

Set Default Goal Selector "!".

Open Scope subst_scope.

Definition ctx := list (level * term).

Notation "'∙'" :=
  (@nil (level * term)).

Notation "Γ ,, d" :=
  (@cons (level * term) d Γ) (at level 20, d at next level).

Notation "Γ ,,, Δ" :=
  (@List.app (level * term) Δ Γ) (at level 25, Δ at next level, left associativity).