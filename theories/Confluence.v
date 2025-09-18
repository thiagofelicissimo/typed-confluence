(** * Typing *)

From Stdlib Require Import Utf8 List Arith Bool Lia.
From TypedConfluence.autosubst
Require Import core unscoped AST SubstNotations RAsimpl AST_rasimpl.
From TypedConfluence Require Import Util BasicAST Weakenings Contexts Typing. (*  Env Inst. *)
From Stdlib Require Import Setoid Morphisms Relation_Definitions.

Reserved Notation "Γ ⊢< l > t ⟹ u : T" (at level 50, l, t, u, T at next level).
Import CombineNotations.

Inductive ortho_red : ctx -> level -> term -> term → term → Prop :=

| ortho_var :
    ∀ Γ x l A,
      ⊢ Γ -> 
      nth_error Γ x = Some (l , A) →
      (Γ ⊢< l > (var x) ⟹ (var x) : ((plus (S x)) ⋅ A))

| ortho_sort :
    ∀ Γ l,
      ⊢ Γ -> 
      Γ ⊢< Ax (Ax l) > Sort l ⟹ Sort l : Sort (Ax l)

| ortho_pi :
    ∀ Γ i j A B A' B',
      Γ ⊢< Ax i > A ⟹ A' : Sort i →
      Γ ,, (i , A) ⊢< Ax j > B ⟹ B' : Sort j →
      Γ ⊢< Ax (Ru i j) > Pi i j A B ⟹ Pi i j A' B' : Sort (Ru i j)

| ortho_lam :
    ∀ Γ i j A B t A' B' t',
      Γ ⊢< Ax i > A ≡ A' : Sort i →
      Γ ,, (i , A) ⊢< Ax j > B ≡ B': Sort j →
      Γ ,, (i , A) ⊢< j > t ⟹ t' : B →
      Γ ⊢< Ru i j > lam i j A B t ⟹ lam i j A' B' t' : Pi i j A B

| ortho_app :
    ∀ Γ i j A B t u A' B' t' u',
      Γ ⊢< Ax i > A ≡ A' : Sort i →
      Γ ,, (i , A) ⊢< Ax j > B ≡ B': Sort j →
      Γ ⊢< Ru i j > t ⟹ t' : Pi i j A B →
      Γ ⊢< i > u ⟹ u' : A →
      Γ ⊢< j > app i j A B t u ⟹ app i j A' B' t' u' : B <[ u .. ] 

| ortho_nat :
    ∀ Γ,
      ⊢ Γ -> 
      Γ ⊢< ty 1 > Nat ⟹ Nat : Sort (ty 0)

| ortho_zero : 
    ∀ Γ,
      ⊢ Γ -> 
      Γ ⊢< ty 0 > zero ⟹ zero : Nat

| ortho_succ : 
    ∀ Γ t t', 
      Γ ⊢< ty 0 > t ⟹ t' : Nat ->
      Γ ⊢< ty 0 > succ t ⟹ succ t' : Nat

| ortho_rec : 
    ∀ Γ l P p_zero p_succ t P' p_zero' p_succ' t',
      Γ ,, (ty 0 , Nat) ⊢< Ax l > P ⟹ P' : Sort l ->
      Γ ⊢< l > p_zero ⟹ p_zero' : P <[ p_zero .. ] -> 
      Γ ,, (ty 0 , Nat) ,, (l , P <[ (var 0) .. ]) ⊢< l > p_succ ⟹ p_succ' : P <[ (succ (var 0)) .. ] ->
      Γ ⊢< ty 0 > t ⟹ t' : Nat ->
      Γ ⊢< l > rec l P p_zero p_succ t ⟹ rec l P' p_zero' p_succ' t' : P <[ t .. ]
  
| ortho_conv : 
    ∀ Γ l A B t t',
      Γ ⊢< l > t ⟹ t' : A -> 
      Γ ⊢< Ax l > A ≡ B : Sort l ->
      Γ ⊢< l > t ⟹ t' : B

| ortho_irrel : 
    ∀ Γ A t t',
      Γ ⊢< prop > t : A -> 
      Γ ⊢< prop > t' : A ->
      Γ ⊢< prop > t ⟹ t' : A

| ortho_beta : 
    ∀ Γ i j A1 B1 t u A2 B2 t' u',
      Γ ⊢< Ax i > A1 ≡ A2 : Sort i →
      Γ ,, (i , A1) ⊢< Ax j > B1 ≡ B2 : Sort j →
      Γ ,, (i , A1) ⊢< j > t ⟹ t' : B1 →
      Γ ⊢< i > u ⟹ u' : A1 →
      Γ ⊢< j > app i j A1 B1 (lam i j A2 B2 t) u ⟹ t' <[ u' .. ] : B1 <[ u .. ] 

| ortho_eta : 
    ∀ Γ i j A1 B1 t A2 B2 t',
      Γ ⊢< Ax i > A1 ≡ A2 : Sort i →
      Γ ,, (i , A1) ⊢< Ax j > B1 ≡ B2 : Sort j →
      Γ ⊢< Ru i j > t ⟹ t' : Pi i j A1 B1 →
      let t_wk := wk_tm (_wk_step _wk_id) t in 
      let A2_wk := wk_tm (_wk_step _wk_id) A2 in 
      let B2_wk := wk_tm (_wk_up (_wk_step _wk_id)) B2 in (* is this right? *)
      Γ ⊢< Ru i j > lam i j A1 B1 (app i j A2_wk B2_wk t_wk (var 0)) ⟹ t' : Pi i j A1 B1

| ortho_rec_zero : 
    ∀ Γ l P p_zero p_succ p_zero',
      Γ ,, (ty 0 , Nat) ⊢< Ax l > P : Sort l ->
      Γ ⊢< l > p_zero ⟹ p_zero' : P <[ p_zero .. ] -> 
      Γ ,, (ty 0 , Nat) ,, (l , P <[ (var 0) .. ]) ⊢< l > p_succ : P <[ (succ (var 0)) .. ] ->
      Γ ⊢< l > rec l P p_zero p_succ zero ⟹ p_zero' : P <[ zero .. ]

| ortho_rec_succ : 
    ∀ Γ l P p_zero p_succ t P' p_zero' p_succ' t',
      Γ ,, (ty 0 , Nat) ⊢< Ax l > P ⟹ P' : Sort l ->
      Γ ⊢< l > p_zero ⟹ p_zero' : P <[ p_zero .. ] -> 
      Γ ,, (ty 0 , Nat) ,, (l , P <[ (var 0) .. ]) ⊢< l > p_succ ⟹ p_succ' : P <[ (succ (var 0)) .. ] ->
      Γ ⊢< ty 0 > t ⟹ t' : Nat ->
      Γ ⊢< l > rec l P p_zero p_succ (succ t) ⟹ 
          p_succ' <[ t' .: (rec l P' p_zero' p_succ' t') ..] : P <[ (succ t) .. ]
  

where "Γ ⊢< l > t ⟹ u : A" := (ortho_red Γ l t u A).


Reserved Notation "Γ ⊢s σ ⟹ τ : Δ" (at level 50, σ, τ, Δ at next level).

Inductive ortho_subst (Γ : ctx) : ctx -> (nat -> term) -> (nat -> term) -> Prop :=
  | well_sempty (σ σ' : nat -> term) : 
    Γ ⊢s σ ⟹ σ' : ∙
  | well_scons (σ σ' : nat -> term) (Δ : ctx) l (A : term) :
    Γ ⊢s (↑ >> σ) ⟹ (↑ >> σ') : Δ ->
    Γ ⊢< l > σ var_zero ⟹ σ' var_zero : A <[↑ >> σ] ->
    Γ ⊢s σ ⟹ σ' : (Δ ,, (l , A)) 
where "Γ ⊢s σ ⟹ τ : Δ" := (ortho_subst Γ Δ σ τ).

Theorem ortho_refl : 
  forall Γ l t A, 
    Γ ⊢< l > t : A -> 
    Γ ⊢< l > t ⟹ t : A.
Admitted.

Theorem ortho_to_conv : 
  forall Γ l t u A,
    Γ ⊢< l > t ⟹ u : A -> 
    Γ ⊢< l > t ≡ u : A.
Admitted.

Theorem ortho_validity : 
  forall Γ l t u A,
    Γ ⊢< l > t ⟹ u : A -> 
    (Γ ⊢< l > t : A) /\ (Γ ⊢< l > u : A).
Admitted.

Theorem ortho_wk :
  forall Γ Δ l t u A ρ, 
  ⊢ Δ -> 
  ρ : Γ ⊆ Δ ->
  Γ ⊢< l > t ⟹ u : A -> 
  Δ ⊢< l > (wk_tm ρ t) ⟹ (wk_tm ρ u) : (wk_tm ρ A).
Admitted.

Theorem ortho_conv_in_ctx :
  forall Γ Δ l t u A, 
  ⊢ Γ ≡ Δ -> 
  Γ ⊢< l > t ⟹ u : A -> 
  Δ ⊢< l > t ⟹ u : A.
Admitted.

Theorem ortho_subst_property : 
  forall Γ l t u A Δ σ τ, 
    Δ ⊢s σ ⟹ τ : Γ -> 
    Γ ⊢< l > t ⟹ u : A -> 
    Δ ⊢< l > (t <[ σ ]) ⟹ (u <[ τ ]) : A <[ σ ].
Admitted.

(* the diamond property at sort prop is trivial *)

Theorem ortho_diamond_prop : 
  forall Γ t t' t'' A,
    Γ ⊢< prop > t ⟹ t' : A ->
    Γ ⊢< prop > t ⟹ t'' : A ->
    exists t''', (Γ ⊢< prop > t' ⟹ t''' : A) /\ (Γ ⊢< prop > t'' ⟹ t''' : A).
Proof.
  intros.
  apply ortho_validity in H. destruct H.
  apply ortho_validity in H0. destruct H0.
  exists t.
  split; apply ortho_irrel; auto.
Qed. 

(* to prove the diamond property, an induction on t will not work, because in rule eta the subject of the premises are not subterms of t. 
  we instead need a measure stable under weakenings, like the size of t. *)


Fixpoint size (t : term) : nat := 
  match t with 
  | var _ => 0
  | Sort _ => 0
  | Pi _ _ A B => 1 + size A + size B
  | lam _ _ A B t => 1 + size A + size B + size t
  | app _ _ A B t u => 1 + size A + size B + size t + size u
  | Nat => 0
  | zero => 0
  | succ t => 1 + size t
  | rec _ P p0 ps t => 1 + size P + size p0 + size ps + size t
end.

Theorem size_ren t f : size t = size (ren_term f t).
Proof.
  generalize f.
  induction t; auto; intros; simpl.
  - rewrite (IHt1 f0). rewrite (IHt2 (upRen_term_term f0)). lia.
  - rewrite (IHt1 f0). rewrite (IHt2 (upRen_term_term f0)).  rewrite (IHt3 (upRen_term_term f0)). lia.
  - rewrite (IHt1 f0). rewrite (IHt2 (upRen_term_term f0)).  rewrite (IHt3 f0). rewrite (IHt4 f0). lia.
  - rewrite (IHt f0). lia.
  - rewrite (IHt1 (upRen_term_term f0)). rewrite (IHt2 f0). rewrite (IHt3 (upRen_term_term (upRen_term_term f0))). rewrite (IHt4 f0). lia.
Qed.

Theorem size_wk t ρ : size t = size (wk_tm ρ t).
Proof.
  apply size_ren.
Qed.


Theorem ortho_diamond : 
  forall Γ i t t' t'' A,
    Γ ⊢< ty i > t ⟹ t' : A ->
    Γ ⊢< ty i > t ⟹ t'' : A ->
    exists t''', (Γ ⊢< ty i > t' ⟹ t''' : A) /\ (Γ ⊢< ty i > t'' ⟹ t''' : A).
Proof.
  intros Γ i. 
  refine (@well_founded_ind _ (fun t u => size t > size u) _ _ _).
  admit.
  intros.
  (* now we need an inversion principle for Γ ⊢< ty i > t ⟹ t' : A and  Γ ⊢< ty i > t ⟹ t'' : A 
    which only requires us to consider compatible derivation rules, and which removes conversion *)
Admitted.


