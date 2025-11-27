(** * Typing *)

From Stdlib Require Import Utf8 List Arith Bool Lia Wellfounded.Inverse_Image Wellfounded.Inclusion.
From TypedConfluence
Require Import core unscoped Ast SubstNotations RAsimpl AST_rasimpl.
From TypedConfluence Require Import Util BasicAST Weakenings Contexts Typing BasicMetaTheory. (*  Env Inst. *)
From Stdlib Require Import Setoid Morphisms Relation_Definitions.
(* Require Import Stdlib.Program.Equality. *)
Require Import Equations.Prop.DepElim.
From Equations Require Import Equations.

Reserved Notation "Γ ⊢< l > t ⟹ u : T" (at level 50, l, t, u, T at next level).
Import CombineNotations.

Inductive ortho_red : ctx -> level -> term -> term → term → Prop :=

| ortho_var :
    ∀ Γ x l A,
      ⊢ Γ ->
      Γ ∋< l > x : A →
      Γ ⊢< l > var x ⟹ var x : A

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
      Γ ⊢< l > p_zero ⟹ p_zero' : P <[ zero .. ] ->
      Γ ,, (ty 0 , Nat) ,, (l , P) ⊢< l > p_succ ⟹ p_succ' : P <[ (succ (var 1)) .: (shift >> (shift >> var)) ]  ->
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

(* | ortho_eta :
    ∀ Γ i j A1 B1 t A2 B2 t',
      Γ ⊢< Ax i > A1 ≡ A2 : Sort i →
      Γ ,, (i , A1) ⊢< Ax j > B1 ≡ B2 : Sort j →
      Γ ⊢< Ru i j > t ⟹ t' : Pi i j A1 B1 →
      let t_wk := wk_tm (_wk_step _wk_id) t in
      let A2_wk := wk_tm (_wk_step _wk_id) A2 in
      let B2_wk := wk_tm (_wk_up (_wk_step _wk_id)) B2 in (* is this right? *)
      Γ ⊢< Ru i j > lam i j A1 B1 (app i j A2_wk B2_wk t_wk (var 0)) ⟹ t' : Pi i j A1 B1 *)

| ortho_rec_zero :
    ∀ Γ l P p_zero p_succ p_zero',
      Γ ,, (ty 0 , Nat) ⊢< Ax l > P : Sort l ->
      Γ ⊢< l > p_zero ⟹ p_zero' : P <[ zero .. ] ->
      Γ ,, (ty 0 , Nat) ,, (l , P) ⊢< l > p_succ : P <[ (succ (var 1)) .: (shift >> (shift >> var)) ]  ->
      Γ ⊢< l > rec l P p_zero p_succ zero ⟹ p_zero' : P <[ zero .. ]

| ortho_rec_succ :
    ∀ Γ l P p_zero p_succ t P' p_zero' p_succ' t',
      Γ ,, (ty 0 , Nat) ⊢< Ax l > P ⟹ P' : Sort l ->
      Γ ⊢< l > p_zero ⟹ p_zero' : P <[ zero .. ] ->
      Γ ,, (ty 0 , Nat) ,, (l , P) ⊢< l > p_succ ⟹ p_succ' : P <[ (succ (var 1)) .: (shift >> (shift >> var)) ]  ->
      Γ ⊢< ty 0 > t ⟹ t' : Nat ->
      Γ ⊢< l > rec l P p_zero p_succ (succ t) ⟹
          p_succ' <[  (rec l P' p_zero' p_succ' t') .: t' ..] : P <[ (succ t) .. ]


where "Γ ⊢< l > t ⟹ u : A" := (ortho_red Γ l t u A).


Reserved Notation "Γ ⊢s σ ⟹ τ : Δ" (at level 50, σ, τ, Δ at next level).

Inductive ortho_subst (Γ : ctx) : ctx -> (nat -> term) -> (nat -> term) -> Prop :=
  | ortho_sempty (σ σ' : nat -> term) :
    Γ ⊢s σ ⟹ σ' : ∙
  | ortho_scons (σ σ' : nat -> term) (Δ : ctx) l (A : term) :
    Γ ⊢s (↑ >> σ) ⟹ (↑ >> σ') : Δ ->
    Γ ⊢< l > σ var_zero ⟹ σ' var_zero : A <[↑ >> σ] ->
    Γ ⊢s σ ⟹ σ' : (Δ ,, (l , A))
where "Γ ⊢s σ ⟹ τ : Δ" := (ortho_subst Γ Δ σ τ).


(* --- Basic properties of ortho: reflexivity, included in conv, weakening, substitution, conv in ctx, etc --- *)

Theorem ortho_refl :
  forall Γ l t A,
    Γ ⊢< l > t : A ->
    Γ ⊢< l > t ⟹ t : A.
Proof.
  intros. induction H; eauto using ortho_red, conv_refl.
Qed.


Theorem ortho_to_conv :
  forall Γ l t u A,
    Γ ⊢< l > t ⟹ u : A ->
    Γ ⊢< l > t ≡ u : A.
Proof.
  intros.
  induction H; eauto using conversion, validity_conv_left.
  - eapply conv_trans.
    + eapply conv_app; eauto using validity_conv_left.
      eapply conv_conv.
      ++ eapply conv_lam; eauto using validity_conv_right.  1,2: eapply conv_refl; eauto using conv_ty_in_ctx_ty, conv_sym, validity_conv_right.
        eauto using conv_conv, conv_ty_in_ctx_conv.
      ++ eapply conv_pi; eauto using conv_sym, conv_ty_in_ctx_conv, validity_conv_right.
    + eapply conv_conv.
      eapply conv_beta; eauto using validity_conv_right, conv_ty_in_ctx_ty, type_conv.
      eapply subst_conv; eauto using conv_sym, validity_conv_ctx, substs_one.
  - eapply conv_trans. eapply conv_rec_succ; eauto using validity_conv_left.
    eapply subst_conv; eauto using validity_conv_ctx.
    2:rasimpl;reflexivity.
    eapply conv_scons_alt. eapply substs_one; eauto.
    eapply conv_rec'; eauto.
Qed.


Lemma ortho_validity_left Γ l t u A :
  Γ ⊢< l > t ⟹ u : A ->
  Γ ⊢< l > t : A.
Proof.
  intros. eauto using ortho_to_conv, validity_conv_left. 
Qed.

Lemma ortho_validity_right Γ l t u A :
  Γ ⊢< l > t ⟹ u : A ->
  Γ ⊢< l > u : A.
Proof.
  intros. eauto using ortho_to_conv, validity_conv_right. 
Qed.

Lemma ortho_meta_conv Γ u v l A B :
  Γ ⊢< l > u ⟹ v : A →
  A = B →
  Γ ⊢< l > u ⟹ v : B.
Proof.
  intros ? ->. auto.
Qed.

Lemma ortho_meta_conv2 Γ u v v' l A B :
  Γ ⊢< l > u ⟹ v : A →
  A = B →
  v = v' ->
  Γ ⊢< l > u ⟹ v' : B.
Proof.
  intros. subst. auto.
Qed.


Theorem ortho_ren Γ l t u A ρ Δ :
  Γ ⊢< l > t ⟹ u : A →
  ⊢ Δ →
  Δ ⊢r ρ : Γ →
  Δ ⊢< l > ρ ⋅ t ⟹ ρ ⋅ u : ρ ⋅ A.
Proof.
  intros. generalize Δ ρ H0 H1. clear Δ ρ H0 H1.
  induction H.
  all: try solve [ intros ; try econstructor ; eauto 6 using WellRen_up, ctx_cons, ortho_validity_left, conv_ren, validity_conv_left, type_ren, type_nat ].
  all: try solve [
    intros ; cbn in * ; (eapply meta_conv + eapply meta_conv_conv + eapply ortho_meta_conv) ; [
      econstructor ; 
      (* (eapply meta_conv + eapply meta_conv_conv + eapply ortho_meta_conv + idtac);  *)
      eauto 8 using WellRen_up, ctx_cons, ortho_validity_left, conv_ren, validity_conv_left, type_ren, type_nat, ortho_meta_conv
    | rasimpl ; reflexivity
    ]
  ].
  - intros.
    cbn. constructor. 1: auto.
    eapply varty_ren. all: eassumption.
  - intros. cbn. eapply ortho_meta_conv. eapply ortho_rec. 
    (* all:(eapply meta_conv + eapply meta_conv_conv + eapply ortho_meta_conv + idtac).
    all:eauto 8 using WellRen_up, ctx_cons, ortho_validity_left, conv_ren, validity_conv_left, type_ren, type_nat, ortho_meta_conv.*)
    all:eauto. 4:rasimpl;eauto.
    1:eapply IHortho_red1; eauto using WellRen_up, ctx_cons, ortho_validity_left, conv_ren, validity_conv_left, type_ren, type_nat.
    eauto 9 using ortho_meta_conv, WellRen_up, ctx_cons, ortho_validity_left, conv_ren, validity_conv_left, type_ren, type_nat, eq_refl.
    
    eapply ortho_meta_conv. eapply IHortho_red2; eauto using WellRen_up, ctx_cons, ortho_validity_left, conv_ren, validity_conv_left, type_ren, type_nat.
    rasimpl. reflexivity.

    eapply ortho_meta_conv. eapply IHortho_red3; eauto 9 using WellRen_up, ctx_cons, ortho_validity_left, conv_ren, validity_conv_left, type_ren, type_nat.
    rasimpl. reflexivity.
  - intros. cbn. eapply ortho_meta_conv2. 
    eapply ortho_beta; eauto 7 using conv_ren, ctx_cons, WellRen_up, ortho_validity_left, type_ren, validity_conv_left.
    all:rasimpl;reflexivity.
  - intros. cbn. eapply ortho_meta_conv. eapply ortho_rec_zero; eauto using conv_ren, ctx_cons, WellRen_up, ortho_validity_left, type_ren, validity_conv_left, type_nat.
    eapply ortho_meta_conv. eapply IHortho_red; eauto. rasimpl. reflexivity.
    eapply type_ren; eauto. eauto 8 using ctx_cons, type_nat, type_ren, WellRen_up.
    eapply WellRen_up; eauto. eapply WellRen_up; eauto.
    all:rasimpl;reflexivity.
  - intros. cbn. eapply ortho_meta_conv2. eapply ortho_rec_succ; eauto using WellRen_up, ctx_cons, ortho_validity_left, conv_ren, validity_conv_left, type_ren, type_nat.
    eapply ortho_meta_conv. eapply IHortho_red2;  eauto.
    2:eapply ortho_meta_conv. 
    2:eapply IHortho_red3; eauto 9 using WellRen_up, ctx_cons, ortho_validity_left, conv_ren, validity_conv_left, type_ren, type_nat.
    all: ssimpl; reflexivity.
Qed.

Theorem ortho_subst_refl :
  forall Γ σ Δ,
  Γ ⊢s σ : Δ ->
  Γ ⊢s σ ⟹ σ : Δ.
Proof.
  intros.
  induction H; eauto using ortho_subst.
  econstructor; eauto using ortho_refl.
Qed.

Lemma subst_ortho_var Γ l x τ σ Δ A : 
  Δ ⊢s σ ⟹ τ : Γ -> 
  Γ ∋< l > x : A ->
  Δ ⊢< l > σ x ⟹ τ x : A <[ σ].
Proof.
  intros. generalize σ τ Δ H. clear σ τ Δ H.  induction H0; intros. 
  - dependent destruction H. rasimpl in H0. rasimpl. eauto.
  - rasimpl. eapply (IHvarty (S >> σ) (S >> τ)). dependent destruction H. eauto.
Qed. 


Lemma ortho_subst_up Γ Δ l A A' σ τ :
  Γ ⊢s σ ⟹ τ : Δ →
  A' = A <[ σ ] ->
  Γ ⊢< Ax l > A <[ σ ] : Sort l ->
  Γ ,, (l, A') ⊢s up_term σ ⟹ up_term τ : Δ ,, (l, A).
Proof.
  intros. subst.
  constructor.
Admitted.


Theorem subst_ortho Γ l t u A σ τ Δ :
  Γ ⊢< l > t ⟹ u : A →
  ⊢ Δ →
  Δ ⊢s σ ⟹ τ : Γ →
  Δ ⊢< l > t <[σ] ⟹ u<[τ] : A<[σ].
Proof.
  intros. generalize Δ σ τ H0 H1. clear Δ σ τ H0 H1.
  induction H.
  all: try solve [ intros ; try econstructor ; eauto 9 using WellSubst_up, ctx_cons, ortho_validity_left, subst_ty, subst_conv, refl_subst, validity_conv_left
  ].
  all: try solve [
    intros ; cbn in * ; (eapply meta_conv + eapply meta_conv_conv + eapply ortho_meta_conv) ; [
      econstructor ; 
      (* (eapply meta_conv + eapply meta_conv_conv + eapply ortho_meta_conv + idtac);  *)
      eauto 9 using WellSubst_up, ctx_cons, ortho_validity_left, subst_ty, subst_conv, refl_subst, validity_conv_left
      (* , ortho_validity_left, conv_ren, validity_conv_left, type_ren, type_nat, ortho_meta_conv *)
    | rasimpl ; reflexivity
    ]
  ].
  (* - intros.
    cbn. eapply subst_ortho_var; eauto.
  - intros. cbn. eapply ortho_meta_conv. eapply ortho_pi ; eauto. eapply IHortho_red2.
  - intros. cbn. eapply ortho_meta_conv. eapply ortho_rec; eauto 9 using WellSubst_up, ctx_cons, ortho_validity_left, subst_ty, subst_conv, refl_subst, validity_conv_left, type_nat.
    + eapply ortho_meta_conv. eapply IHortho_red2; eauto.
      rasimpl. reflexivity.
    + eapply ortho_meta_conv. eapply IHortho_red3; eauto.
      eauto 10 using ctx_cons, type_nat, subst_ty, ortho_validity_left, WellSubst_up.
      eapply WellSubst_up. eapply WellSubst_up. all: eauto using type_nat.
      eapply subst_ty; eauto using ctx_cons, type_nat, ortho_validity_left.
      eapply WellSubst_up; eauto using type_nat.
      rasimpl. reflexivity.
    + rasimpl. reflexivity.
  - intros. cbn. eapply ortho_meta_conv2. eapply ortho_beta; eauto 9 using WellSubst_up, ctx_cons, ortho_validity_left, subst_ty, subst_conv, refl_subst, validity_conv_left, type_nat.
     all:rasimpl;reflexivity.
  - intros. cbn. eapply ortho_meta_conv2. eapply ortho_rec_zero; eauto.
    + eapply subst_ty; eauto using ctx_cons, type_nat. eapply WellSubst_up; eauto using type_nat.
    + eapply ortho_meta_conv. eapply IHortho_red; eauto. rasimpl. reflexivity.
    + eapply subst_ty; eauto. 
      eapply ctx_cons; eauto using ctx_cons, type_nat, subst_ty, WellSubst_up.
      eapply subst_ty; eauto using ctx_cons, type_nat. eapply WellSubst_up; eauto using type_nat.
      eapply WellSubst_up. eapply WellSubst_up. 
      all:eauto using type_nat.
      eapply subst_ty; eauto using ctx_cons, type_nat. eapply WellSubst_up; eauto using type_nat.
      rasimpl. reflexivity.
    + rasimpl. reflexivity.
    + rasimpl. reflexivity.
  - intros. cbn. eapply ortho_meta_conv2. eapply ortho_rec_succ; eauto 9 using WellSubst_up, ctx_cons, ortho_validity_left, subst_ty, subst_conv, refl_subst, validity_conv_left, type_nat.
    + eapply ortho_meta_conv. eapply IHortho_red2; eauto. rasimpl. reflexivity.
    + eapply ortho_meta_conv. eapply IHortho_red3; eauto.
      eapply ctx_cons; eauto using ctx_cons, type_nat, subst_ty, WellSubst_up.
      eapply subst_ty; eauto using ctx_cons, type_nat, ortho_validity_left. eapply WellSubst_up; eauto using type_nat.
      eapply WellSubst_up. eapply WellSubst_up. 
      all:eauto using type_nat.
      eapply subst_ty; eauto using ctx_cons, type_nat, ortho_validity_left. eapply WellSubst_up; eauto using type_nat.
      rasimpl. reflexivity.
    + rasimpl. reflexivity.
    + rasimpl. reflexivity.
Qed. *)
Admitted.

Theorem ortho_conv_in_ctx :
  forall Γ Δ l t u A,
  ⊢ Γ ≡ Δ ->
  Γ ⊢< l > t ⟹ u : A ->
  Δ ⊢< l > t ⟹ u : A.
Proof.
  intros.
  eapply subst_ortho with (σ := var) (τ := var) in H0. 
  - rasimpl in H0. eassumption.
  - eauto using validity_ctx_conv_right.
  - eapply ortho_subst_refl. eapply WellSubst_conv; eauto using ctx_conv_sym, subst_id, validity_ctx_conv_right.
Qed.




(* --- Inversion principles for ⟹ --- *)


Lemma ortho_var_inv Γ i x t A :
  Γ ⊢< ty i > var x ⟹ t : A →
  ∃ B,
    t = var x  ∧
    Γ ∋< ty i > x : B.
Proof.
  intros.
  dependent induction H; eauto. 
Qed.


Lemma ortho_sort_inv Γ l l' t A :
  Γ ⊢< l' > Sort l ⟹ t : A →
  t = Sort l  ∧ l' = Ax (Ax l).
Proof.
  intros.
  dependent induction H; eauto.
  assert (Γ ⊢< Ax (Ax l) > Sort l : Sort (Ax l)) by eauto using type_sort,validity_ty_ctx.
  eapply sort_unicity in H; eauto. destruct l; inversion H.
Qed.


Lemma ortho_pi_inv Γ l1 l2 l' t' A B T :
  Γ ⊢< l' > Pi l1 l2 A B ⟹ t' : T →
  exists A' B',
    t' = Pi l1 l2 A' B'  ∧
    l' =  Ax (Ru l1 l2) ∧
    Γ ⊢< Ax l1 > A ⟹ A' : Sort l1 ∧
    Γ ,, (l1 , A) ⊢< Ax l2 > B ⟹ B' : Sort l2 ∧
    Γ ⊢< Ax (Ax (Ru l1 l2)) > Sort (Ru l1 l2) ≡ T : Sort (Ax (Ru l1 l2)).
Proof.
  intros.
  dependent induction H; eauto.
  - eauto 10 using ortho_to_conv, validity_conv_ctx, conv_sort.
  - destruct IHortho_red as (A' & B' & eq & eq' & redA & redB & conv). subst.
    eauto 8 using conv_sym, conv_trans.
  - eapply type_inv in H as (_ & _ & eq & _).
    destruct l1; inversion eq.
Qed.

Lemma ortho_lam_inv Γ i l1 l2 A1 B1 t u T :
  Γ ⊢< ty i > lam l1 l2 A1 B1 t ⟹ u : T →
  exists A1' B1' t',
    ty i = Ru l1 l2 ∧
    Γ ⊢< Ax (Ru l1 l2) > Pi l1 l2 A1 B1 ≡ T : Sort (Ru l1 l2)  ∧
    u = lam l1 l2 A1' B1' t' ∧
    Γ ⊢< Ax l1 > A1 ≡ A1' : Sort l1 ∧
    Γ ,, (l1 , A1) ⊢< Ax l2 > B1 ≡ B1' : Sort l2 ∧
    Γ ,, (l1 , A1) ⊢< l2 > t ⟹ t' : B1.
Proof.
  intros.
  dependent induction H; eauto.
  (* destruct (IHortho_red _ _ _ _ _ _ _ _ _ eq_refl). *)
  - rewrite H2 in *. clear H2.
    eauto 13 using conv_pi, validity_conv_left, conv_refl.

  - destruct IHortho_red as (A' & B' & t'' & eq & conv & eq' & convA & convB & red). subst.
    rewrite <- eq in *. clear eq.
    eauto 10 using conv_sym, conv_trans.
Qed.

Lemma ortho_app_inv Γ i l1 l2 A1 B1 t u w T :
  Γ ⊢< ty i > app l1 l2 A1 B1 t u ⟹ w : T →
  ty i = l2 ∧
  Γ ⊢< Ax l2 > B1 <[ u .. ] ≡ T : Sort l2  ∧
  ((
    (* by app cong *)
    exists A1' B1' t' u',
      w = app l1 l2 A1' B1' t' u' ∧
      Γ ⊢< Ax l1 > A1 ≡ A1' : Sort l1 ∧
      Γ ,, (l1 , A1) ⊢< Ax l2 > B1 ≡ B1' : Sort l2 ∧
      Γ ⊢< Ru l1 l2 > t ⟹ t' : Pi l1 l2 A1 B1  ∧
      Γ ⊢< l1 > u ⟹ u' : A1
  ) \/ (
    (* by beta *)
    exists A2 B2 v v' u',
      t = lam l1 l2 A2 B2 v  ∧
      Γ ⊢< Ax l1 > A1 ≡ A2 : Sort l1 ∧
      Γ ,, (l1 , A1) ⊢< Ax l2 > B1 ≡ B2 : Sort l2 ∧
      Γ ,, (l1 , A1) ⊢< l2 > v ⟹ v' : B1  ∧
      Γ ⊢< l1 > u ⟹ u' : A1  ∧
      w = v' <[ u' .. ]
  )).
Proof.
  intros.
  dependent induction H; eauto.
  - split; eauto. split; eauto 8 using validity_conv_left, ortho_validity_left, subst_conv, substs_one, validity_conv_ctx, conv_refl.
    left. eauto 9.
  - destruct IHortho_red as (eq & conv & disj).
    subst. split; eauto. split; eauto using conv_sym, conv_trans.
  - split; eauto. split; eauto 8 using validity_conv_left, ortho_validity_left, subst_conv, substs_one, validity_conv_ctx, conv_refl.
    right. eauto 11.
Qed.





Lemma ortho_nat_inv Γ l' t A :
  Γ ⊢< l' > Nat ⟹ t : A → t = Nat.
Proof.
  intros.
  dependent induction H; eauto. dependent induction H. apply IHtyping; eauto. eapply type_conv; eauto using conv_sym.
Qed.

Lemma ortho_zero_inv Γ l' t A :
  Γ ⊢< l' > zero ⟹ t : A → t = zero.
Proof.
  intros.
  dependent induction H; eauto. dependent induction H. apply IHtyping; eauto. eapply type_conv; eauto using conv_sym.
Qed.

Lemma ortho_succ_inv Γ l' t n A :
  Γ ⊢< l' > succ n ⟹ t : A →
  exists n',
    t = succ n' /\
    Γ ⊢< ty 0 > n ⟹ n' : Nat.
Proof.
  intros.
  dependent induction H; eauto. dependent induction H. apply IHtyping; eauto. eapply type_conv; eauto using conv_sym.
Qed.

Lemma ortho_rec_inv Γ i l P p_zero p_succ u t T :
  Γ ⊢< ty i > rec l P p_zero p_succ u ⟹ t : T →
  ( (* by rec cong *)
    exists P' p_zero' p_succ' u',
      t = rec l P' p_zero' p_succ' u' ∧
      Γ ,, (ty 0, Nat) ⊢< Ax l > P ⟹ P' : Sort l ∧
      Γ ⊢< l > p_zero ⟹ p_zero' : P <[ zero ..] ∧
      Γ ,, (ty 0, Nat) ,, (l, P) ⊢< l > p_succ ⟹ p_succ' : P <[ (succ (var 1)) .: (shift >> (shift >> var)) ]  ∧
      Γ ⊢< ty 0 > u ⟹ u' : Nat
  ) \/ ( (* by ortho_zero *)
    exists p_zero',
      t = p_zero' ∧ u = zero ∧
      Γ ⊢< l > p_zero ⟹ p_zero' : P <[ zero ..]
  ) \/ ( (* by ortho_succ *)
    exists P' p_zero' p_succ' n n',
      t = p_succ' <[ (rec l P' p_zero' p_succ' n') .: n' ..] ∧ u = succ n ∧
      Γ ,, (ty 0, Nat) ⊢< Ax l > P ⟹ P' : Sort l ∧
      Γ ⊢< l > p_zero ⟹ p_zero' : P <[ zero ..] ∧
      Γ ,, (ty 0, Nat) ,, (l, P) ⊢< l > p_succ ⟹ p_succ' : P <[ (succ (var 1)) .: (shift >> (shift >> var)) ]   ∧
      Γ ⊢< ty 0 > n ⟹ n' : Nat).
Proof.
  intros.
  dependent induction H.
  - left. do 4 eexists. split. reflexivity. eauto.
  - eapply IHortho_red.
  - right. left. eauto.
  - right. right. do 5 eexists. split. reflexivity. split. reflexivity. eauto.
Qed.

Lemma ortho_box_inv Γ l' t A :
  Γ ⊢< l' > box ⟹ t : A → False.
Proof.
  intros.
  dependent induction H; eauto. dependent induction H. eapply IHtyping; eauto.
Qed.

Ltac ttinv h :=
  lazymatch type of h with
  _ ⊢< _ > ?t ⟹ _ : _ =>
    lazymatch t with
    | var _ => eapply ortho_var_inv in h
    | Sort _ => eapply ortho_sort_inv in h
    | Pi _ _ _ _ => eapply ortho_pi_inv in h
    | lam _ _ _ _ _ => eapply ortho_lam_inv in h
    | app _ _ _ _ _ _ => eapply ortho_app_inv in h
    | Nat => eapply ortho_nat_inv in h
    | zero => eapply ortho_zero_inv in h
    | succ _ => eapply ortho_succ_inv in h
    | rec _ _ _ _ _ => eapply ortho_rec_inv in h
    | box => eapply ortho_box_inv in h
    end
  end.

(* --- Aux lemmas to help automation in the next proofs --- *)

Lemma red_scons_id Γ l A t t' :
  Γ ⊢< l > t ⟹ t' : A ->
  Γ ⊢s t .. ⟹ t' .. : Γ ,, (l , A).
Proof.
  intro t_red_t'.
  apply ortho_scons; ssimpl; eauto using subst_id, ortho_subst_refl, ortho_validity_left, validity_ty_ctx.
Qed.

Lemma red_scons_id_2 Γ l A t t' u u' l' B :
  Γ ⊢< l > t ⟹ t' : A ->
  Γ ⊢< l' > u ⟹ u' : B <[ t .. ] ->
  Γ ⊢s (u .: t ..) ⟹ (u' .: t' ..) : (Γ ,, (l , A)) ,, (l', B).
Proof.
  intros t_red_t' u_red_u'.
  apply ortho_scons. apply ortho_scons.
  all: (ssimpl; eauto 6 using ortho_subst_refl, subst_id, ortho_to_conv, validity_conv_left, validity_ty_ctx).
Qed.

Lemma conv_ty_in_ctx_ortho Γ l A A' l' t u B :
  Γ ,, (l , A) ⊢< l' > t ⟹ u : B ->
  Γ ⊢< Ax l > A ≡ A' : Sort l ->
  Γ ,, (l , A') ⊢< l' > t ⟹ u : B.
Proof.
  intros t_red_u A_eq_A'.
  eapply ortho_conv_in_ctx; eauto.
  apply conv_ccons; eauto using ctx_conv_refl, validity_ty_ctx, validity_conv_left.
Qed.

Lemma ctx_from_conv Γ A B l : 
  Γ ⊢< Ax l > A ≡ B : Sort l ->
  ⊢ Γ ,, (l , A).
Proof.
  intros.
  eapply validity_conv_left in H. econstructor; eauto using validity_ty_ctx.
Qed.


(* Lemma ctx_from_red Γ A B l : 
  Γ ⊢< Ax l > A ⟹ B : Sort l ->
  ⊢ Γ ,, (l , A).
Proof.
  intros.
  eapply ortho_validity_left in H. econstructor; eauto using validity_ty_ctx.
Qed. *)

(* --- Proof of the diamond property --- *)

(* the measure we are going to use *)
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
  | box => 0
end.

(* allows us to close the diamond with different types in the two ends *)
Lemma ortho_diamond_helper Γ l t t' t'' A :
  Γ ⊢< l > t ⟹ t' : A ->
  Γ ⊢< l > t ⟹ t'' : A ->
    (exists B C l' l'' t''', (Γ ⊢< l' > t' ⟹ t''' : B) /\ (Γ ⊢< l'' > t'' ⟹ t''' : C)) ->
    exists t''', (Γ ⊢< l > t' ⟹ t''' : A) /\ (Γ ⊢< l > t'' ⟹ t''' : A).
Proof.
  intros t_red_t' t_red_t'' [B [C [l' [l'' [t''' [t'_red_t''' t''_red_t''']]]]]].
  apply ortho_validity_right in t_red_t' as t'_A.
  apply ortho_validity_right in t_red_t'' as t''_A.
  apply ortho_validity_left in t'_red_t''' as t'_B.
  apply ortho_validity_left in t''_red_t''' as t''_C.
  rewrite <- (sort_unicity _ _ _ _ _ _ t'_A t'_B) in *.
  rewrite <- (sort_unicity _ _ _ _ _ _ t''_A t''_C) in *.
  exists t'''.
  split; eauto using ortho_conv, type_unicity, conv_sym.
Qed.


(* the diamond property at sort prop is trivial *)
Theorem ortho_diamond_prop Γ t t' t'' A :
    Γ ⊢< prop > t ⟹ t' : A ->
    Γ ⊢< prop > t ⟹ t'' : A ->
    exists t''', (Γ ⊢< prop > t' ⟹ t''' : A) /\ (Γ ⊢< prop > t'' ⟹ t''' : A).
Proof.
  intros.
  exists t.
  split; apply ortho_irrel; eauto using ortho_validity_left, ortho_validity_right.
Qed.


(* when applied to the ih, allows to also consider the more general case in which l can be prop.
   this allows us to avoid doing a case analysis on l in the middle of the proof. *)
Lemma ortho_diamond_helper2 u :
  (forall t, size t < size u -> forall Γ i t' t'' A , Γ ⊢< ty i > t ⟹ t' : A ->
  Γ ⊢< ty i > t ⟹ t'' : A ->
  exists t''', (Γ ⊢< ty i > t' ⟹ t''' : A) /\ (Γ ⊢< ty i > t'' ⟹ t''' : A))
  -> forall t, size t < size u -> forall Γ l t' t'' A,
  Γ ⊢< l > t ⟹ t' : A ->
  Γ ⊢< l > t ⟹ t'' : A ->
  exists t''', (Γ ⊢< l > t' ⟹ t''' : A) /\ (Γ ⊢< l > t'' ⟹ t''' : A).
Proof.
  intros.
  destruct l.
  - apply (H _ H0); auto.
  - apply (ortho_diamond_prop _ _ _ _ _ H1 H2).
Qed.

(* the main proof *)
Theorem ortho_diamond_ty :
  forall Γ i t t' t'' T,
    Γ ⊢< ty i > t ⟹ t' : T ->
    Γ ⊢< ty i > t ⟹ t'' : T ->
    exists t''', (Γ ⊢< ty i > t' ⟹ t''' : T) /\ (Γ ⊢< ty i > t'' ⟹ t''' : T).
Proof.
  intros Γ i t. generalize t Γ i. clear Γ i t.

  refine (@well_founded_ind _ (fun t u => size t < size u) _ _ _).
  eapply wf_inverse_image, lt_wf.
  intros t IH Γ i t' t'' T t_red_t' t_red_t''.

  destruct t.
  all : eapply (ortho_diamond_helper _ _ _ _ _ _ t_red_t' t_red_t'').
  all : pose proof (IH' := ortho_diamond_helper2 _ IH); clear IH; rename IH' into IH.
  all : assert (⊢ Γ) as ΓWf by (apply ortho_validity_left in t_red_t'; apply validity_ty_ctx in t_red_t' as ΓWf; eapply validity_ty_ty in t_red_t' as tyWf; auto).

  (* var *)
  - ttinv t_red_t'. destruct t_red_t' as (B' & t'_eq_n & lookup_n_B).
    rewrite t'_eq_n in *. clear t'_eq_n t'.
    ttinv t_red_t''. destruct t_red_t'' as (_ & t''_eq_n & _).
    rewrite t''_eq_n in *. clear t''_eq_n t''.
    do 4 eexists. exists (var n). split; apply ortho_var; eauto.


  (* sort *)
  - ttinv t_red_t'. destruct t_red_t' as (t'_eq_sort & i_eq_ax).
    rewrite t'_eq_sort in *. clear t'_eq_sort t'.
    ttinv t_red_t''. destruct t_red_t'' as (t''_eq_sort & _).
    rewrite t''_eq_sort in *. clear t''_eq_sort t''.
    do 4 eexists. exists (Sort l). split; apply ortho_sort; eauto.


  (* pi *)
  - rename t1 into A. rename t2 into B.
    ttinv t_red_t'. destruct t_red_t' as (A' & B' & t'_eq_pi & _ & A_red_A' & B_red_B' & _).
    rewrite t'_eq_pi in *. clear t'_eq_pi t'.
    ttinv t_red_t''. destruct t_red_t'' as (A'' & B'' & t''_eq_pi & _ & A_red_A'' & B_red_B'' & _).
    rewrite t''_eq_pi in *. clear t''_eq_pi t''.

    destruct (IH A ltac:(simpl; lia) _ _ _ _ _ A_red_A' A_red_A'') as (A''' & A'_red_A''' & A''_red_A''').
    destruct (IH B ltac:(simpl; lia) _ _ _ _ _ B_red_B' B_red_B'') as (B''' & B'_red_B''' & B''_red_B''').
    do 4 eexists. exists (Pi l l0 A''' B''').
    split; apply ortho_pi; eauto 7 using conv_ty_in_ctx_ortho, ortho_to_conv, conv_refl, validity_ty_ty, validity_conv_left.

  (* lam *)
  - rename t1 into A. rename t2 into B. rename t3 into u.
    ttinv t_red_t'. destruct t_red_t' as (A' & B' & u' & _ & _ & t'_eq_lam & A_conv_A' & B_conv_B' & u_red_u').
    rewrite t'_eq_lam in *. clear t'_eq_lam t'.
    ttinv t_red_t''. destruct t_red_t'' as (A'' & B'' & u'' & _ & _ & t''_eq_lam & A_conv_A'' & B_conv_B'' & u_red_u'').
    rewrite t''_eq_lam in *. clear t''_eq_lam t''.

    destruct (IH u ltac:(simpl; lia) _ _ _ _ _ u_red_u' u_red_u'') as (u''' & u'_red_u''' & u''_red_u''').

    do 4 eexists. exists (lam l l0 A B u''').
    split; apply ortho_lam; eauto using conv_ty_in_ctx_ortho, ortho_conv, conv_ty_in_ctx_conv, conv_sym.

  (* app *)
  - rename t1 into A. rename t2 into B. rename t3 into u. rename t4 into v.
    ttinv t_red_t'.
    destruct t_red_t' as
      (i_eq & _ & [ (A' & B' & u' & v' & t'_eq & A_conv_A' & B_conv_B' & u_red_u' & v_red_v')
      | (A0 & B0 & w & w' & v' & u_eq & A_conv_A0 & B_conv_B0  & w_red_w' & v_red_v' & t'_eq) ]);
    ttinv t_red_t'';
    destruct t_red_t'' as
      (_ & _ & [ (A'' & B'' & u'' & v'' & t''_eq & A_conv_A'' & B_conv_B'' & u_red_u'' & v_red_v'')
      | (A0_ & B0_ & w_ & w'' & v'' & u_eq_ & A_conv_A0_ & B_conv_B0_ & w_red_w'' & v_red_v'' & t''_eq) ]);
    try rewrite t'_eq in *; clear t'_eq t'; rewrite t''_eq in *; clear t''_eq t'';
    try destruct (IH u ltac:(simpl; lia) _ _ _ _ _ u_red_u' u_red_u'') as (u''' & u'_red_u''' & u''_red_u''');
    try destruct (IH v ltac:(simpl; lia) _ _ _ _ _ v_red_v' v_red_v'') as (v''' & v'_red_v''' & v''_red_v''').

    (* app-cong x app-cong *)
    + do 4 eexists. exists (app l l0 A B u''' v''').
    split; apply ortho_app; eauto using conv_sym, conv_ty_in_ctx_conv, conv_ty_in_ctx_ortho, conv_sym, ortho_conv, conv_pi, validity_conv_left.

    (* app-cong x beta *)
    + rename u_eq_ into u_eq. rename w_ into w. rename A0_ into A0.
      rename B0_ into B0. rename A_conv_A0_ into A_conv_A0. rename B_conv_B0_ into B_conv_B0.

      rewrite u_eq in *. clear u_eq u. rewrite <- i_eq in *. clear l0 i_eq.

      ttinv u_red_u'. destruct u_red_u' as (A0' & B0' & w' & _ & _ & u'_eq & A0_conv_A0' & B0_conv_B0' & w_red_w').

      rewrite u'_eq in *. clear u'_eq u'.

      rename w_red_w' into temp.
      assert (Γ,, (l, A) ⊢< ty i > w ⟹ w' : B) as w_red_w'. {eauto using conv_ty_in_ctx_ortho, conv_sym, ortho_conv. }
      clear temp.

      destruct (IH w ltac:(simpl; lia) _ _ _ _ _ w_red_w' w_red_w'') as (w''' & w'_red_w''' & w''_red_w''').

      do 4 eexists. exists (w''' <[ v''' ..]). split.
      ++ eapply ortho_beta; eauto 7 using conv_sym, conv_trans, ortho_conv, conv_ty_in_ctx_ortho, conv_ty_in_ctx_conv.
      ++ eauto using red_scons_id, subst_ortho.

    (* beta x app-cong *)
    (* roughly a copy-and-paste from the above *)
    + rewrite u_eq in *. clear u_eq u. rewrite <- i_eq in *. clear l0 i_eq.

      ttinv u_red_u''. destruct u_red_u'' as (A0'' & B0'' & w'' & _ & _ & u''_eq & A0_conv_A0'' & B0_conv_B0'' & w_red_w'').

      rewrite u''_eq in *. clear u''_eq u''.

      rename w_red_w'' into temp.
      assert (Γ,, (l, A) ⊢< ty i > w ⟹ w'' : B) as w_red_w''. {eauto using conv_ty_in_ctx_ortho, conv_sym, ortho_conv. }
      clear temp.

      destruct (IH w ltac:(simpl; lia) _ _ _ _ _ w_red_w' w_red_w'') as (w''' & w'_red_w''' & w''_red_w''').

      do 4 eexists. exists (w''' <[ v''' ..]). split.
      ++ eauto using red_scons_id, subst_ortho.
      ++ eapply ortho_beta; eauto 7 using conv_sym, conv_trans, ortho_conv, conv_ty_in_ctx_ortho, conv_ty_in_ctx_conv.

    (* beta x beta *)
    + rewrite u_eq in *. clear u_eq u.
      inversion u_eq_.  rewrite <- H2 in *. clear A_conv_A0_ B_conv_B0_ H0 H1 H2 u_eq_ w_ A0_ B0_.

      destruct (IH w ltac:(simpl; lia) _ _ _ _ _ w_red_w' w_red_w'') as (w''' & w'_red_w''' & w''_red_w''').

      do 4 eexists. exists (w''' <[ v''' .. ]).  split; eauto using subst_ortho, red_scons_id.


  (* Nat *)
  - ttinv t_red_t'. rewrite t_red_t'. clear t' t_red_t'.
    ttinv t_red_t''. rewrite t_red_t''. clear t'' t_red_t''.
    do 4 eexists. exists Nat. split; apply ortho_nat; eauto.

  (* zero *)
  - ttinv t_red_t'. rewrite t_red_t'. clear t' t_red_t'.
    ttinv t_red_t''. rewrite t_red_t''. clear t'' t_red_t''.
    do 4 eexists. exists zero. split; apply ortho_zero; eauto.

  (* succ *)
  - rename t into n.
    ttinv t_red_t'. destruct t_red_t' as (n' & t'_eq & n_red_n').
    rewrite t'_eq. clear t'_eq t'.
    ttinv t_red_t''. destruct t_red_t'' as (n'' & t''_eq & n_red_n'').
    rewrite t''_eq. clear t''_eq t''.

    destruct (IH n ltac:(simpl; lia) _ _ _ _ _ n_red_n' n_red_n'') as (n''' & n'_red_n''' & n''_red_n''').

    do 4 eexists. exists (succ n'''). split; eapply ortho_succ; eauto.

  (* rec *)
  - rename t1 into P. rename t2 into p_zero. rename t3 into p_succ. rename t4 into n.
    ttinv t_red_t'. ttinv t_red_t''.
    destruct t_red_t' as
      [(P' & p_zero' & p_succ' & n' & t'_eq & P_red_P' & p_zero_red_p_zero' & p_succ_red_p_succ' & n_red_n')
      | [ (p_zero' & t'_eq & n_eq & p_zero_red_p_zero')
      | (P' & p_zero' & p_succ' & m & m' & t'_eq & n_eq & P_red_P' & p_zero_red_p_zero' & p_succ_red_p_succ' & m_red_m') ]];
    destruct t_red_t'' as
      [(P'' & p_zero'' & p_succ'' & n'' & t''_eq & P_red_P'' & p_zero_red_p_zero'' & p_succ_red_p_succ'' & n_red_n'')
      | [ (p_zero'' & t''_eq & n_eq_ & p_zero_red_p_zero'')
      | (P'' & p_zero'' & p_succ'' & k & k'' & t''_eq & n_eq_ & P_red_P'' & p_zero_red_p_zero'' & p_succ_red_p_succ'' & k_red_k'')]];
    try rewrite t'_eq in *; try clear t'_eq t'; try rewrite t''_eq in *; try clear t''_eq t'';
    try rewrite n_eq in *; try rewrite n_eq_ in *; try clear n_eq n; try clear n_eq_ n;
    try destruct (IH P ltac:(simpl; lia) _ _ _ _ _ P_red_P' P_red_P'') as (P''' & P'_red_P''' & P''_red_P''');
    try destruct (IH p_zero ltac:(simpl; lia) _ _ _ _ _ p_zero_red_p_zero' p_zero_red_p_zero'')
      as (p_zero''' & p_zero'_red_p_zero''' & p_zero''_red_p_zero''');
    try destruct (IH p_succ ltac:(simpl; lia) _ _ _ _ _ p_succ_red_p_succ' p_succ_red_p_succ'')
      as (p_succ''' & p_succ'_red_p_succ''' & p_succ''_red_p_succ''').

    (* rec x rec *)
    + destruct (IH n ltac:(simpl; lia) _ _ _ _ _ n_red_n' n_red_n'') as (n''' & n'_red_n''' & n''_red_n''').

      do 4 eexists. exists (rec l P''' p_zero''' p_succ''' n''').

      split; eapply ortho_rec; 
      eauto 11 using ortho_conv, subst_conv, subst_one, type_zero, conv_ty_in_ctx_ortho, ortho_to_conv, subst_id_var1, ortho_validity_left, ctx_from_conv, refl_subst.

    (* rec x rec_zero *)
    + ttinv n_red_n'. rewrite n_red_n' in *. clear n' n_red_n'.

      do 4 eexists. exists p_zero'''. split.
      2 : eauto.
      eapply ortho_rec_zero;
      eauto 12 using conv_ty_in_ctx_ortho, ortho_to_conv, subst_conv, ortho_conv, ortho_validity_left,
                ortho_validity_right, subst_id_var1, subst_one, type_zero, ctx_from_conv, refl_subst.

    (* rec x rec_succ *)
    + ttinv n_red_n'. destruct n_red_n' as (k' & n'_eq & k_red_k'). rewrite n'_eq in *. clear n' n'_eq.
      destruct (IH k ltac:(simpl; lia) _ _ _ _ _ k_red_k' k_red_k'') as (k''' & k'_red_k''' & k''_red_k''').

      do 4 eexists. exists ( p_succ''' <[ (rec l P''' p_zero''' p_succ''' k''') .: k''' ..]). split.
      ++ eapply ortho_rec_succ;
          eauto 11 using conv_ty_in_ctx_ortho, subst_conv, ortho_to_conv, subst_id_var1,
                    subst_one, ortho_conv, type_zero, ortho_validity_left, ctx_from_conv, refl_subst.
      ++ eapply subst_ortho; eauto. apply red_scons_id_2; eauto.
        eapply ortho_conv.
        +++ eapply ortho_rec;
          eauto 11 using conv_ty_in_ctx_ortho, subst_conv, ortho_to_conv, subst_id_var1,
                    subst_one, ortho_conv, type_zero, ortho_validity_left, ctx_from_conv, refl_subst.
        +++ eauto 7 using subst_conv, ortho_to_conv, conv_sym, subst_one, ortho_validity_left, refl_subst.

    (* rec_zero x rec *)
    (* roughly a copy-and-paste from the above *)
    + ttinv n_red_n''. rewrite n_red_n'' in *. clear n'' n_red_n''.

      do 4 eexists. exists p_zero'''. split.
      1 : eauto.
      eapply ortho_rec_zero;
      eauto 12 using conv_ty_in_ctx_ortho, ortho_to_conv, subst_conv, ortho_conv, ortho_validity_left,
                ortho_validity_right, subst_id_var1, subst_one, type_zero, ctx_from_conv, refl_subst.
    (* rec_zero x rec_zero *)
    + do 4 eexists. exists p_zero'''. split; eauto.

    (* rec_zero x rec_succ *)
    + inversion n_eq_.

    (* rec_succ x rec *)
    (* roughly a copy-and-paste from the above *)
    + ttinv n_red_n''. destruct n_red_n'' as (m'' & n''_eq & m_red_m''). rewrite n''_eq in *. clear n'' n''_eq.
      destruct (IH m ltac:(simpl; lia) _ _ _ _ _ m_red_m' m_red_m'') as (m''' & m'_red_m''' & m''_red_m''').

      do 4 eexists. exists ( p_succ''' <[ (rec l P''' p_zero''' p_succ''' m''') .: m''' ..]). split.
      ++ eapply subst_ortho; eauto. apply red_scons_id_2; eauto.
        eapply ortho_conv.
        +++ eapply ortho_rec;
          eauto 11 using conv_ty_in_ctx_ortho, subst_conv, ortho_to_conv, subst_id_var1,
                    subst_one, ortho_conv, type_zero, ortho_validity_left, ctx_from_conv, refl_subst.
        +++ eauto 7 using subst_conv, ortho_to_conv, conv_sym, subst_one, ortho_validity_left, refl_subst.
      ++ eapply ortho_rec_succ;
          eauto 11 using conv_ty_in_ctx_ortho, subst_conv, ortho_to_conv, subst_id_var1,
                    subst_one, ortho_conv, type_zero, ortho_validity_left, ctx_from_conv, refl_subst.

    (* rec_succ x rec_zero *)
    + inversion n_eq_.

    (* rec_succ x rec_succ *)
    + inversion n_eq_. rewrite H0 in *. clear m H0 n_eq_.
      rename m' into k'. rename m_red_m' into k_red_k'.
      destruct (IH k ltac:(simpl; lia) _ _ _ _ _ k_red_k' k_red_k'') as (k''' & k'_red_k''' & k''_red_k''').
      do 4 eexists. exists (p_succ''' <[ rec l P''' p_zero''' p_succ''' k''' .: k''' .. ]).
      split; eapply subst_ortho; eauto.
      all : apply red_scons_id_2; eauto.
      all : eapply ortho_conv.
      1,3: eapply ortho_rec;
        eauto 11 using ortho_rec, ortho_conv, subst_conv, subst_one, type_zero,
                  ortho_to_conv, conv_ty_in_ctx_ortho, ortho_validity_left, subst_id_var1, ctx_from_conv, refl_subst.
      1,2: eauto 7 using subst_conv, ortho_to_conv, conv_sym, subst_one, ortho_validity_left, refl_subst.

  (* box *)
  - ttinv t_red_t'. easy.
Qed.

Corollary diamond :
  forall Γ l t t' t'' T,
    Γ ⊢< l > t ⟹ t' : T ->
    Γ ⊢< l > t ⟹ t'' : T ->
    exists t''', (Γ ⊢< l > t' ⟹ t''' : T) /\ (Γ ⊢< l > t'' ⟹ t''' : T).
Proof.
  intros Γ l t t' t'' T t_red_t' t_red_t''.
  destruct l.
  - apply (ortho_diamond_ty _ _ t t' t''); auto.
  - apply (ortho_diamond_prop _ t t' t''); auto.
Qed.

(* --- Proof of confluence --- *)

Inductive ortho_redd Γ l A : term -> term -> Prop :=
  | redd_step t u : Γ ⊢< l > t ⟹ u : A -> ortho_redd Γ l A t u
  | redd_trans t u v : ortho_redd Γ l A t v -> ortho_redd Γ l A v u -> ortho_redd Γ l A t u.

Notation "Γ ⊢< l > t ⟹* t' : A" := (ortho_redd Γ l A t t') (at level 50, l, t, t', A at next level).


Lemma confluence_aux Γ l t t' t'' A :
  Γ ⊢< l > t ⟹ t' : A ->
  Γ ⊢< l > t ⟹* t'' : A ->
  exists t''', Γ ⊢< l > t' ⟹* t''' : A /\ Γ ⊢< l > t'' ⟹ t''' : A.
Proof.
  intros t_red_t' t_redd_t''. generalize t' t_red_t'. clear t' t_red_t'.
  induction t_redd_t''; intros.
  - pose (K := diamond _ _ _ _ _ _ H t_red_t').
    destruct K as (t''' & K1 & K2). exists t'''. split; eauto using redd_step.
  - pose (K := IHt_redd_t''1 _ t_red_t'). destruct K as (t''' & K1 & K2).
    pose (K := IHt_redd_t''2 _ K2). destruct K as (s & K3 & K4).
    exists s. split; eauto using redd_trans.
Qed.

Lemma confluence Γ l t t' t'' A :
  Γ ⊢< l > t ⟹* t' : A ->
  Γ ⊢< l > t ⟹* t'' : A ->
  exists t''', Γ ⊢< l > t' ⟹* t''' : A /\ Γ ⊢< l > t'' ⟹* t''' : A.
Proof.
  intro t_red_t'. generalize t''. clear t''.
  induction t_red_t'; intros.
  - pose (K := confluence_aux _ _ _ _ _ _ H H0). destruct K as (v & K1 & K2). exists v; eauto using redd_step.
  - pose (K := IHt_red_t'1 _ H). destruct K as (t''' & K1 & K2).
    pose (K := IHt_red_t'2 _ K1). destruct K as (s & K3 & K4).
    exists s. split; eauto using redd_trans.
Qed.

(* --- Proof that the equiv closure of ⟹ and ≡ are the same (surprisingly hard!) --- *)

Inductive ortho_equiv Γ l A : term -> term -> Prop :=
  | equiv_step t u : Γ ⊢< l > t ⟹ u : A -> ortho_equiv Γ l A t u
  | equiv_trans t u v : ortho_equiv Γ l A t v -> ortho_equiv Γ l A v u -> ortho_equiv Γ l A t u
  | equiv_sym t u : ortho_equiv Γ l A u t -> ortho_equiv Γ l A t u.

Notation "Γ ⊢< l > t ≈ t' : A" := (ortho_equiv Γ l A t t') (at level 50, l, t, t', A at next level).



Lemma redd_to_conv Γ l t u A :
  Γ ⊢< l > t ⟹* u : A ->
  Γ ⊢< l > t ≡ u : A.
Proof.
  intro t_redd_u.
  induction t_redd_u; eauto using ortho_to_conv, conv_trans.
Qed.

(* the easy direction *)
Lemma equiv_to_conv Γ l t u A :
  Γ ⊢< l > t ≈ u : A ->
  Γ ⊢< l > t ≡ u : A.
Proof.
  intro t_equiv_u.
  induction t_equiv_u; eauto using ortho_to_conv, conv_trans, conv_sym.
Qed.




Lemma equiv_conv Γ l A B t t' :
      Γ ⊢< l > t ≈ t' : A ->
      Γ ⊢< Ax l > A ≡ B : Sort l ->
      Γ ⊢< l > t ≈ t' : B.
Proof.
  intros t_equiv_t' A_conv_B.
  induction t_equiv_t'.
  - apply equiv_step. eapply ortho_conv; eauto.
  - eapply equiv_trans; eauto.
  - eapply equiv_sym; eauto.
Qed.

(* The typed version of lemma equiv_red_ind from Theo's local_comp.
   Going from the original untyped version to this typed one took me a lot of trial and error. *)
Lemma equiv_red_ind {Γ Δ l A i} P f :
    (forall t u, Δ ⊢< i > t ≡ u : A -> Γ ⊢< l > f t : P t <-> Γ ⊢< l > f u : P u) ->
    (forall t u, Δ ⊢< i > t ⟹ u : A -> Γ ⊢< l > f t : P t -> Γ ⊢< l > f t ≈ f u : P t) ->
    forall {t u}, Δ ⊢< i > t ≈ u : A -> Γ ⊢< l > f t : P t -> Γ ⊢< l > f t ≈ f u : P t.
Proof.
  intros. induction H1.
  - eauto.
  - apply equiv_to_conv in H1_ as t_eq_v.
    apply H in t_eq_v as temp.
    apply temp in H2 as fv_Pv.
    clear temp.
    apply IHortho_equiv1 in H2 as ft_equiv_fv.
    apply IHortho_equiv2 in fv_Pv as fv_equiv_fu.
    apply equiv_to_conv in ft_equiv_fv as ft_eq_fv.
    apply validity_conv_right in ft_eq_fv as fv_Pt.
    assert (Γ ⊢< Ax l > P t ≡ P v : Sort l) as Pt_eq_Pv by eauto using type_unicity.
    eapply equiv_trans.
    apply ft_equiv_fv.
    eapply equiv_conv.
    eapply fv_equiv_fu.
    eauto using conv_sym.
  - apply equiv_to_conv in H1 as u_eq_t.
    apply H in u_eq_t as temp.
    apply temp in H2 as fu_Pu.
    apply IHortho_equiv in fu_Pu.
    apply equiv_to_conv in fu_Pu as  K.
    apply validity_conv_right in K.
    assert (Γ ⊢< Ax l > P t ≡ P u : Sort l) by eauto using type_unicity.
    eapply equiv_sym.
    eapply equiv_conv.
    apply fu_Pu.
    eauto using conv_sym.
Qed.


(* Lemma aux Γ l t t' A l' B B' :
  Γ ⊢< l > t ≡ t' : A ->
  Γ ,, (l , A) ⊢< Ax l' > B ≡ B' : Sort l' ->
  Γ ⊢< Ax l' > B <[ t..] ≡ B' <[ t'..] : Sort l'.
Proof.
  intros.
  assert (Γ ⊢< Ax (Ax l') > (Sort l') <[ t.. ] ≡ Sort l' : Sort (Ax l'))
    by eauto using conv_sort, validity_ty_ctx, validity_conv_left.
  eapply conv_conv; eauto.
  eapply subst; eauto.
  eapply conv_scons; ssimpl; eauto using subst_id, refl_subst, validity_ty_ctx, validity_conv_left.
Qed. *)



Lemma equiv_pi Γ i j A B A' B' :
      Γ ⊢< Ax i > A ≈ A' : Sort i →
      Γ ,, (i , A) ⊢< Ax j > B ≈ B' : Sort j →
      Γ ⊢< Ax (Ru i j) > Pi i j A B ≈ Pi i j A' B' : Sort (Ru i j).
Proof.
  intros A_equiv_A' B_equiv_B'.
  eapply equiv_trans.
  - refine (equiv_red_ind (fun _ => Sort (Ru i j)) (fun B => Pi i j A B) _ _ B_equiv_B' _).
    3 : eauto 6 using type_pi, equiv_to_conv, validity_conv_left.
    + intros. split; eauto using type_pi, equiv_to_conv, validity_conv_left, validity_conv_right.
    + intros. apply equiv_step. eauto using ortho_pi, equiv_to_conv, validity_conv_left, ortho_refl.
  - refine (equiv_red_ind (fun _ => Sort (Ru i j)) (fun A => Pi i j A B') _ _ A_equiv_A' _).
    3 : eauto 6 using type_pi, equiv_to_conv, validity_conv_left, validity_conv_right.
    + intros.
      split; intro temp; apply type_inv in temp as (H1 & H2 & _);
      eauto using type_pi, validity_conv_right, validity_conv_left, conv_sym, conv_ty_in_ctx_ty.
    + intros v v' v_red_v' Wt. apply type_inv in Wt as (v_Wt & B_Wt & _).
      apply equiv_step. eauto using ortho_pi, ortho_refl, conv_ty_in_ctx_ty.
Qed.


Lemma equiv_lam Γ i j A B t A' B' t' :
      Γ ⊢< Ax i > A ≡ A' : Sort i →
      Γ ,, (i , A) ⊢< Ax j > B ≡ B': Sort j →
      Γ ,, (i , A) ⊢< j > t ≈ t' : B →
      Γ ⊢< Ru i j > lam i j A B t ≈ lam i j A' B' t' : Pi i j A B.
Proof.
  intros.
  eapply equiv_trans.
  - refine (equiv_red_ind (fun _ => Pi i j A B) (fun t => lam i j A B t) _ _ H1 _).
    3 : eauto 6 using equiv_to_conv, type_lam, validity_conv_left.
    + intros v v' v_red_v'. split; eauto using type_lam, validity_conv_left, validity_conv_right.
    + intros. apply equiv_step. eauto 6 using ortho_lam, validity_conv_left, conv_refl.
  - eapply equiv_step. eauto using equiv_to_conv, ortho_lam, validity_conv_right, ortho_refl.
Qed.

Lemma equiv_app Γ i j A B t u A' B' t' u' :
      Γ ⊢< Ax i > A ≡ A' : Sort i →
      Γ ,, (i , A) ⊢< Ax j > B ≡ B': Sort j →
      Γ ⊢< Ru i j > t ≈ t' : Pi i j A B →
      Γ ⊢< i > u ≈ u' : A →
      Γ ⊢< j > app i j A B t u ≈ app i j A' B' t' u' : B <[ u .. ].
Proof.
  intros.
  eapply equiv_trans. eapply equiv_trans.
  - refine (equiv_red_ind (fun _ => B <[ u ..]) (fun t => app i j A B t u) _ _ H1 _).
    3: eauto 8 using type_app, equiv_to_conv, validity_conv_left.
    + intros. split; eauto 7 using equiv_to_conv, validity_conv_left, validity_conv_right, type_app.
    + intros. apply equiv_step.
      eauto 9 using ortho_app, equiv_to_conv, validity_conv_left, ortho_refl, conv_refl.
  - refine (equiv_red_ind (fun u => B <[ u ..]) (fun u => app i j A B t' u) _ _ H2 _).
    3:eauto 8 using type_app, equiv_to_conv, validity_conv_left, validity_conv_right.
    + intros. split; eauto 7 using type_app, validity_conv_left, equiv_to_conv, validity_conv_right.
    + intros. eapply equiv_step.
      eauto 9 using ortho_app, equiv_to_conv, validity_conv_left, validity_conv_right, ortho_refl, conv_refl.
  - apply equiv_step. eapply ortho_conv.
    + eauto 8 using ortho_app, validity_conv_right, equiv_to_conv, ortho_refl.
    + eapply subst_conv; eauto using substs_one, equiv_to_conv, validity_conv_ctx, validity_conv_left, conv_refl, conv_sym.
Qed.


Lemma equiv_succ Γ t t' :
      Γ ⊢< ty 0 > t ≈ t' : Nat ->
      Γ ⊢< ty 0 > succ t ≈ succ t' : Nat.
Proof.
  intro t_equiv_t'.
  refine (equiv_red_ind (fun _ => Nat) (fun t => succ t) _ _ t_equiv_t' _).
  3: eauto using type_succ, equiv_to_conv, validity_conv_left.
  - intros. split; eauto using type_succ, validity_conv_left, validity_conv_right.
  - intros. apply equiv_step. eauto using ortho_succ.
Qed.

Lemma equiv_rec Γ l P p_zero p_succ t P' p_zero' p_succ' t' :
      Γ ,, (ty 0 , Nat) ⊢< Ax l > P ≈ P' : Sort l ->
      Γ ⊢< l > p_zero ≈ p_zero' : P <[ zero .. ] ->
      Γ ,, (ty 0 , Nat) ,, (l , P) ⊢< l > p_succ ≈ p_succ' : P <[ (succ (var 1)) .: (shift >> (shift >> var)) ] ->
      Γ ⊢< ty 0 > t ≈ t' : Nat ->
      Γ ⊢< l > rec l P p_zero p_succ t ≈ rec l P' p_zero' p_succ' t' : P <[ t .. ].
Proof.
  intros P_equiv_P' p_zero_equiv_p_zero' p_succ_equiv_p_succ' t_equiv_t'.
  eapply equiv_trans. eapply equiv_trans. eapply equiv_trans.
  - refine (equiv_red_ind (fun _ => P <[ t.. ]) (fun p_zero => rec l P p_zero p_succ t) _ _ p_zero_equiv_p_zero' _).
    3: eauto 10 using type_rec, equiv_to_conv, validity_conv_left.
    + intros. split; eauto 9 using type_rec, equiv_to_conv, validity_conv_left, validity_conv_right.
    + intros. apply equiv_step. eauto 12 using ortho_rec, equiv_to_conv, validity_conv_left, ortho_refl.
  - refine (equiv_red_ind (fun _ => P <[ t.. ]) (fun p_succ => rec l P p_zero' p_succ t) _ _ p_succ_equiv_p_succ' _).
    3: eauto 10 using type_rec, equiv_to_conv, validity_conv_left, validity_conv_right.
    + intros. split; eauto 9 using type_rec, equiv_to_conv, validity_conv_left, validity_conv_right.
    + intros. apply equiv_step.
      eauto 12 using ortho_rec, equiv_to_conv, validity_conv_left, validity_conv_right, ortho_refl.
  - refine (equiv_red_ind (fun t => P <[ t.. ]) (fun t => rec l P p_zero' p_succ' t) _ _ t_equiv_t' _).
    3 : eauto 10 using type_rec, equiv_to_conv, validity_conv_left, validity_conv_right.
    + intros. split; eauto 9 using type_rec, equiv_to_conv, validity_conv_left, validity_conv_right.
    + intros. apply equiv_step.
      eauto 12 using ortho_rec, equiv_to_conv, validity_conv_left, validity_conv_right, ortho_refl.
  - eapply (equiv_conv _ _ (P <[ t'..])).
    2: eapply subst_conv; eauto using substs_one, equiv_to_conv, validity_conv_ctx, validity_conv_left, conv_refl, conv_sym.
    refine (equiv_red_ind (fun P => P <[ t'.. ]) (fun P => rec l P p_zero' p_succ' t') _ _ P_equiv_P' _).
    3 : eauto 10 using type_rec, equiv_to_conv, validity_conv_left, validity_conv_right.
    + intros. split.
      all: (intro temp; apply type_inv in temp; destruct temp as [H1 [H2 [H3 [H4 H5]]]]).
      all: (apply type_rec; eauto 9 using equiv_to_conv, subst_conv, type_conv, type_zero,
        subst_one, validity_ty_ctx, validity_conv_left, conv_sym, conv_ty_in_ctx_ty, subst_id_var1, ctx_from_conv, refl_subst).
    + intros v v' v_red_v' Wt.
      apply type_inv in Wt. destruct Wt as [H1 [H2 [H3 [H4 H5]]]].
      apply equiv_step. eauto using ortho_refl, ortho_rec.
Qed.

Lemma conv_to_equiv Γ l t u A :
  Γ ⊢< l > t ≡ u : A -> Γ ⊢< l > t ≈ u : A.
Proof.
  intro H. induction H.
  1,2,6,7,11,12,13,14 : try solve [apply equiv_step; econstructor; eauto using conv_refl, ortho_refl ].
  all : eauto using equiv_pi, equiv_lam, equiv_app, equiv_succ,
    equiv_rec, equiv_conv, equiv_sym, equiv_trans.
Qed.

(* --- Proof of CR --- *)

Corollary CR Γ l t u A :
  Γ ⊢< l > t ≡ u : A ->
  exists v, Γ ⊢< l > t ⟹* v : A /\ Γ ⊢< l > u ⟹* v : A.
Proof.
  intro H. apply conv_to_equiv in H. induction H.
  - exists u. split; apply redd_step; eauto using ortho_refl, ortho_validity_right.
  - destruct IHortho_equiv1 as (s & t_redd_s & v_redd_s).
    destruct IHortho_equiv2 as (w & v_redd_w & u_redd_w).
    pose (K := confluence _ _ _ _ _ _ v_redd_s v_redd_w).
    destruct K as (x & s_redd_x & w_redd_x).
    exists x. split; eauto using redd_trans.
  - destruct IHortho_equiv as (v & u_redd_v & t_redd_v). exists v. eauto.
Qed.

(* --- Injectivity and non-confusion properties --- *)

Lemma redd_conv_in_ctx Γ Δ l t u A :
  ⊢ Γ ≡ Δ -> Γ ⊢< l > t ⟹* u : A -> Δ ⊢< l > t ⟹* u : A.
Proof.
  intros Γ_equiv_Δ t_redd_u.
  induction t_redd_u.
  - apply redd_step. eapply ortho_conv_in_ctx; eauto.
  - eapply redd_trans; eauto.
Qed.

Lemma pi_redd Γ l l1 l2 A B T U :
  Γ ⊢< l > Pi l1 l2 A B ⟹* T : U ->
  exists A' B',
  T = Pi l1 l2 A' B' /\
  Γ ⊢< Ax l1 > A ⟹* A' : Sort l1 /\
  Γ ,, (l1, A) ⊢< Ax l2 > B ⟹* B' : Sort l2.
Proof.
  intros pi_red_T.
  dependent induction pi_red_T.
  - ttinv H. destruct H as (A' & B' & T_eq & _ & A_red & B_red & _). do 2 eexists. repeat split; eauto using redd_step.
  - destruct IHpi_red_T1 as (A'' & B'' & v_eq & A_red & B_red).
    rewrite v_eq in *. clear v_eq v.
    destruct (IHpi_red_T2 l1 l2 A'' B'' _ eq_refl) as (A''' & B''' & u_eq & A''_red & B''_red).
    rewrite u_eq in *. clear u_eq u.
    exists A'''. exists B'''. repeat split.
    all : (eapply redd_trans; eauto).
    + apply redd_to_conv in A_red. eapply (redd_conv_in_ctx (Γ ,, (l1, A'')));
      eauto 6 using conv_ccons, ctx_conv_refl, conv_sym, validity_conv_left, validity_ty_ctx.
Qed.

Lemma sort_redd Γ l l' t T :
  Γ ⊢< l' > Sort l ⟹* t : T ->
  t = Sort l.
Proof.
  intro sort_redd_t.
  dependent induction sort_redd_t.
  - ttinv H. destruct H. eauto.
  - subst. eauto. 
Qed.

Lemma nat_redd Γ l' t T :
  Γ ⊢< l' > Nat ⟹* t : T ->
  t = Nat.
Proof.
  intro sort_redd_t.
  dependent induction sort_redd_t.
  - ttinv H. eauto.
  - subst. eauto.
Qed.

Proposition sort_inj Γ l i j T :
  Γ ⊢< l > Sort i ≡ Sort j : T -> i = j.
Proof.
  intro sort_eq_sort.
  apply CR in sort_eq_sort.
  destruct sort_eq_sort as (t & sort_redd_t_1 & sort_redd_t_2).
  apply sort_redd in sort_redd_t_1, sort_redd_t_2.
  rewrite sort_redd_t_1 in *. inversion sort_redd_t_2. eauto.
Qed.

Corollary pi_inj Γ l l0 l1 l2 l3 A B A' B' T :
  Γ ⊢< l > Pi l0 l1 A B ≡ Pi l2 l3 A' B' : T ->
  l0 = l2 /\ l1 = l3 /\ Γ ⊢< Ax l0 > A ≡ A' : Sort l0 /\ Γ ,, (l0, A) ⊢< Ax l1 > B ≡ B' : Sort l1.
Proof.
  intro Pi_eq.
  apply CR in Pi_eq.
  destruct Pi_eq as (v & Pi_red_1 & Pi_red_2).
  apply pi_redd in Pi_red_1.
  destruct Pi_red_1 as (A0 & B0 & v_eq & A_redd_A0 & B_redd_B0).
  apply pi_redd in Pi_red_2.
  destruct Pi_red_2 as (A1 & B1 & v_eq_ & A'_redd_A1 & B'_redd_B1).
  rewrite v_eq in *. inversion v_eq_.
  rewrite H0 in *. rewrite H1 in *. rewrite H2 in *. rewrite H3 in *.
  clear A0 B0 H0 H1 H2 H3 v_eq v.
  apply redd_to_conv in A_redd_A0, B_redd_B0, A'_redd_A1, B'_redd_B1.
  split; split; split; auto.
  - eauto using conv_trans, conv_sym.
  - eapply conv_trans. apply B_redd_B0. eauto using conv_ty_in_ctx_conv, conv_sym.
Qed.

Proposition sort_neq_nat Γ l l' T :
  Γ ⊢< l' > Sort l ≡ Nat : T -> False.
Proof.
  intro sort_eq_nat.
  apply CR in sort_eq_nat.
  destruct sort_eq_nat as (t & sort_redd_t & nat_redd_t).
  apply sort_redd in sort_redd_t.
  apply nat_redd in nat_redd_t.
  rewrite sort_redd_t in *.
  inversion nat_redd_t.
Qed.

Proposition sort_neq_pi Γ l l' i j A B T :
  Γ ⊢< l' > Sort l ≡ Pi i j A B : T -> False.
Proof.
  intro sort_eq_pi.
  apply CR in sort_eq_pi.
  destruct sort_eq_pi as (t & sort_redd_t & pi_redd_t).
  apply sort_redd in sort_redd_t.
  apply pi_redd in pi_redd_t as (A' & B' & H & _).
  rewrite sort_redd_t in *.
  inversion H.
Qed.

Proposition nat_neq_pi Γ l' i j A B T :
  Γ ⊢< l' > Nat ≡ Pi i j A B : T -> False.
Proof.
  intro nat_eq_pi.
  apply CR in nat_eq_pi.
  destruct nat_eq_pi as (t & nat_redd_t & pi_redd_t).
  apply nat_redd in nat_redd_t.
  apply pi_redd in pi_redd_t as (A' & B' & H & _).
  rewrite nat_redd_t in *.
  inversion H.
Qed.
