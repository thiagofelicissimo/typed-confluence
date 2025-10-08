(** * Typing *)

From Stdlib Require Import Utf8 List Arith Bool.
From TypedConfluence.autosubst
Require Import core unscoped AST SubstNotations RAsimpl AST_rasimpl.
From TypedConfluence Require Import Util BasicAST Contexts Weakenings. (*  Env Inst. *)
From Stdlib Require Import Setoid Morphisms Relation_Definitions.

Import ListNotations.
Import CombineNotations.

Set Default Goal Selector "!".

Open Scope subst_scope.



Definition Ax (l : level) : level :=
  ty (match l with 
  | prop => 0
  | ty i => S i
  end).

Definition Ru (l1 l2 : level) : level := 
  match l2 with 
  | prop => prop 
  | ty j => ty (match l1 with | prop => j | ty i => max i j end)
  end.


Reserved Notation "Γ ⊢< l > t : T" (at level 50, l, t, T at next level).
Reserved Notation "Γ ⊢< l > t ≡ u : T" (at level 50, l, t, u, T at next level).
Reserved Notation "⊢ Γ" (at level 50).

Inductive typing : ctx -> level -> term → term → Prop :=

| type_var :
    ∀ Γ x l A,
      ⊢ Γ -> 
      nth_error Γ x = Some (l , A) →
      (Γ ⊢< l > (var x) : ((plus (S x)) ⋅ A))

| type_sort :
    ∀ Γ l,
      ⊢ Γ -> 
      Γ ⊢< Ax (Ax l) > Sort l : Sort (Ax l)

| type_pi :
    ∀ Γ i j A B,
      Γ ⊢< Ax i > A : Sort i →
      Γ ,, (i , A) ⊢< Ax j > B : Sort j →
      Γ ⊢< Ax (Ru i j) > Pi i j A B : Sort (Ru i j)


| type_lam :
    ∀ Γ i j A B t,
      Γ ⊢< Ax i > A : Sort i →
      Γ ,, (i , A) ⊢< Ax j > B : Sort j →
      Γ ,, (i , A) ⊢< j > t : B →
      Γ ⊢< Ru i j > lam i j A B t : Pi i j A B

| type_app :
    ∀ Γ i j A B t u,
      Γ ⊢< Ax i > A : Sort i →
      Γ ,, (i , A) ⊢< Ax j > B : Sort j →
      Γ ⊢< Ru i j > t : Pi i j A B →
      Γ ⊢< i > u : A →
      Γ ⊢< j > app i j A B  t u : B <[ u .. ] 

| type_nat :
    ∀ Γ,
      ⊢ Γ -> 
      Γ ⊢< ty 1 > Nat : Sort (ty 0)

| type_zero : 
    ∀ Γ,
      ⊢ Γ -> 
      Γ ⊢< ty 0 > zero : Nat

| type_succ : 
    ∀ Γ t, 
      Γ ⊢< ty 0 > t : Nat ->
      Γ ⊢< ty 0 > succ t : Nat

| type_rec : 
    ∀ Γ l P p_zero p_succ t,
      Γ ,, (ty 0 , Nat) ⊢< Ax l > P : Sort l ->
      Γ ⊢< l > p_zero : P <[ zero .. ] -> 
      Γ ,, (ty 0 , Nat) ,, (l , P) ⊢< l > p_succ : P <[ (succ (var 1)) .: (shift >> (shift >> var)) ] ->
      Γ ⊢< ty 0 > t : Nat ->
      Γ ⊢< l > rec l P p_zero p_succ t : P <[ t .. ]
  
| type_conv : 
    ∀ Γ l A B t,
      Γ ⊢< l > t : A -> 
      Γ ⊢< Ax l > A ≡ B : Sort l ->
      Γ ⊢< l > t : B

with ctx_typing : ctx -> Prop :=
| ctx_nil : 
      ⊢ ∙

| ctx_cons : 
    ∀ Γ l A, 
      ⊢ Γ -> 
      Γ ⊢< Ax l > A : Sort l ->
      ⊢ (Γ ,, (l , A))

with conversion : ctx -> level -> term -> term -> term -> Prop :=


| conv_var :
    ∀ Γ x l A,
      nth_error Γ x = Some (l , A) →
      ⊢ Γ -> 
      (Γ ⊢< l > (var x) ≡ (var x) : ((plus (S x)) ⋅ A))

| conv_sort :
    ∀ Γ l,
      ⊢ Γ ->
      Γ ⊢< Ax (Ax l) > Sort l ≡ Sort l : Sort (Ax l)

| conv_pi :
    ∀ Γ i j A B A' B',
      Γ ⊢< Ax i > A ≡ A' : Sort i →
      Γ ,, (i , A) ⊢< Ax j > B ≡ B' : Sort j →
      Γ ⊢< Ax (Ru i j) > Pi i j A B ≡ Pi i j A' B' : Sort (Ru i j)

| conv_lam :
    ∀ Γ i j A B t A' B' t',
      Γ ⊢< Ax i > A ≡ A' : Sort i →
      Γ ,, (i , A) ⊢< Ax j > B ≡ B': Sort j →
      Γ ,, (i , A) ⊢< j > t ≡ t' : B →
      Γ ⊢< Ru i j > lam i j A B t ≡ lam i j A' B' t' : Pi i j A B

| conv_app :
    ∀ Γ i j A B t u A' B' t' u',
      Γ ⊢< Ax i > A ≡ A' : Sort i →
      Γ ,, (i , A) ⊢< Ax j > B ≡ B': Sort j →
      Γ ⊢< Ru i j > t ≡ t' : Pi i j A B →
      Γ ⊢< i > u ≡ u' : A →
      Γ ⊢< j > app i j A B t u ≡ app i j A' B' t' u' : B <[ u .. ] 

| conv_nat :
    ∀ Γ,
      ⊢ Γ ->
      Γ ⊢< ty 1 > Nat ≡ Nat : Sort (ty 0)

| conv_zero : 
    ∀ Γ,
      ⊢ Γ ->
      Γ ⊢< ty 0 > zero ≡ zero : Nat

| conv_succ : 
    ∀ Γ t t', 
      Γ ⊢< ty 0 > t ≡ t' : Nat ->
      Γ ⊢< ty 0 > succ t ≡ succ t' : Nat

| conv_rec : 
    ∀ Γ l P p_zero p_succ t P' p_zero' p_succ' t',
      Γ ,, (ty 0 , Nat) ⊢< Ax l > P ≡ P' : Sort l ->
      Γ ⊢< l > p_zero ≡ p_zero' : P <[ zero .. ] -> 
      Γ ,, (ty 0 , Nat) ,, (l , P) ⊢< l > p_succ ≡ p_succ' : P <[ (succ (var 1)) .: (shift >> (shift >> var)) ] ->
      Γ ⊢< ty 0 > t ≡ t' : Nat ->
      Γ ⊢< l > rec l P p_zero p_succ t ≡ rec l P' p_zero' p_succ' t' : P <[ t .. ]
  
| conv_conv : 
    ∀ Γ l A B t t',
      Γ ⊢< l > t ≡ t' : A -> 
      Γ ⊢< Ax l > A ≡ B : Sort l ->
      Γ ⊢< l > t ≡ t' : B

| conv_irrel : 
    ∀ Γ A t t',
      Γ ⊢< prop > t : A -> 
      Γ ⊢< prop > t' : A ->
      Γ ⊢< prop > t ≡ t' : A

| conv_beta : 
    ∀ Γ i j A B t u,
      Γ ⊢< Ax i > A : Sort i →
      Γ ,, (i , A) ⊢< Ax j > B : Sort j →
      Γ ,, (i , A) ⊢< j > t : B →
      Γ ⊢< i > u : A →
      Γ ⊢< j > app i j A B (lam i j A B t) u ≡ t <[ u .. ] : B <[ u .. ] 

(* | conv_eta : 
    ∀ Γ i j A B t,
      Γ ⊢< Ax i > A : Sort i →
      Γ ,, (i , A) ⊢< Ax j > B : Sort j →
      Γ ⊢< Ru i j > t : Pi i j A B →
      let t_wk := wk_tm (_wk_step _wk_id) t in 
      let A_wk := wk_tm (_wk_step _wk_id) A in 
      let B_wk := wk_tm (_wk_up (_wk_step _wk_id)) B in (* is this right? *)
      Γ ⊢< Ru i j > lam i j A B (app i j A_wk B_wk t_wk (var 0)) ≡ t : Pi i j A B *)

| conv_rec_zero : 
    ∀ Γ l P p_zero p_succ,
      Γ ,, (ty 0 , Nat) ⊢< Ax l > P : Sort l ->
      Γ ⊢< l > p_zero : P <[ zero .. ] -> 
      Γ ,, (ty 0 , Nat) ,, (l , P) ⊢< l > p_succ : P <[ (succ (var 1)) .: (shift >> (shift >> var)) ]  ->
      Γ ⊢< l > rec l P p_zero p_succ zero ≡ p_zero : P <[ zero .. ]

| conv_rec_succ : 
    ∀ Γ l P p_zero p_succ t,
      Γ ,, (ty 0 , Nat) ⊢< Ax l > P : Sort l ->
      Γ ⊢< l > p_zero : P <[ zero .. ] -> 
      Γ ,, (ty 0 , Nat) ,, (l , P) ⊢< l > p_succ : P <[ (succ (var 1)) .: (shift >> (shift >> var)) ]  ->
      Γ ⊢< ty 0 > t : Nat ->
      Γ ⊢< l > rec l P p_zero p_succ (succ t) ≡ 
          p_succ <[(rec l P p_zero p_succ t) .: t ..] : P <[ (succ t) .. ]

| conv_sym : 
    ∀ Γ l t u A,
      Γ ⊢< l > t ≡ u : A ->
      Γ ⊢< l > u ≡ t : A
  
| conv_trans : 
    ∀ Γ l t u v A,
      Γ ⊢< l > t ≡ u : A ->
      Γ ⊢< l > u ≡ v : A ->
      Γ ⊢< l > t ≡ v : A

where "Γ ⊢< l > t : A" := (typing Γ l t A)
and   "⊢ Γ" := (ctx_typing Γ)
and   "Γ ⊢< l > t ≡ u : A" := (conversion Γ l t u A).


Reserved Notation "Γ ⊢s σ : Δ" (at level 50, σ, Δ at next level).

Reserved Notation "Γ ⊢s σ ≡ τ : Δ" (at level 50, σ, τ, Δ at next level).

Inductive WellSubst (Γ : ctx) : ctx -> (nat -> term) -> Prop :=
  | well_sempty (σ : nat -> term) : 
    Γ ⊢s σ : ∙
  | well_scons (σ : nat -> term) (Δ : ctx) l (A : term) :
    Γ ⊢s (↑ >> σ) : Δ ->
    Γ ⊢< l > σ var_zero : A <[↑ >> σ] ->
    Γ ⊢s σ : (Δ ,, (l , A)) 
where "Γ ⊢s σ : Δ" := (WellSubst Γ Δ σ).

Inductive ConvSubst (Γ : ctx) : ctx -> (nat -> term) -> (nat -> term) -> Prop :=
| conv_sempty (σ τ : nat -> term) : Γ ⊢s σ ≡ τ : ∙
| conv_scons (σ τ : nat -> term) (Δ : ctx) l A :
  Γ ⊢s (↑ >> σ) ≡ (↑ >> τ) : Δ -> 
  Γ ⊢< l > σ var_zero ≡ τ var_zero: A <[↑ >> σ] ->
  Γ ⊢s σ ≡ τ : Δ ,, (l , A)
where "Γ ⊢s σ ≡ τ : Δ" := (ConvSubst Γ Δ σ τ).

Reserved Notation "⊢ Γ ≡ Δ" (at level 50, Δ at next level).

Inductive ConvCtx : ctx -> ctx -> Type :=
| conv_cempty : ⊢ ∙ ≡ ∙
| conv_ccons Γ A Δ B l : 
  ⊢ Γ ≡ Δ -> 
  Γ ⊢< Ax l > A ≡ B : Sort l -> 
  ⊢ (Γ ,, ( l , A)) ≡ (Δ ,, (l , B))
where "⊢ Γ ≡ Δ" := (ConvCtx Γ Δ).
