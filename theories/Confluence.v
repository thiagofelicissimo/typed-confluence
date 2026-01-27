(** * Typing *)

From Stdlib Require Import Utf8 List Arith Bool Lia Wellfounded.Inverse_Image Wellfounded.Inclusion.
From TypedConfluence
Require Import core unscoped Ast SubstNotations RAsimpl AST_rasimpl.
From TypedConfluence Require Import Util BasicAST Contexts Typing BasicMetaTheory.
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

| ortho_Eq :
    ∀ Γ l A A' a a' b b',
      Γ ⊢< Ax l > A ⟹ A' : Sort l ->
      Γ ⊢< l > a ⟹ a' : A ->
      Γ ⊢< l > b ⟹ b' : A ->
      Γ ⊢< Ax prop > Eq l A a b ⟹ Eq l A' a' b' : Sort prop

| ortho_J :
    ∀ Γ l i A A' a a' P P' p p' b b' e e',
      Γ ⊢< Ax l > A ⟹ A' : Sort l ->
      Γ ⊢< l > a ⟹ a' : A ->
      Γ ,, (l , A) ⊢< Ax i > P ⟹ P' : Sort i ->
      Γ ⊢< i > p ⟹ p' : P <[a..] ->
      Γ ⊢< l > b ⟹ b' : A ->
      Γ ⊢< prop > e ⟹ e' : Eq l A a b ->
      Γ ⊢< i > J l i A a P p b e ⟹ J l i A' a' P' p' b' e' : P <[b..]

| ortho_Lift : 
    ∀ Γ l A A',
      Γ ⊢< Ax l > A ⟹ A' : Sort l ->
      Γ ⊢< Ax (Ax l) > Lift l A ⟹ Lift l A' : Sort (Ax l)

| ortho_lift : 
    ∀ Γ l A A' a a',
      Γ ⊢< Ax l > A ≡ A' : Sort l ->
      Γ ⊢< l > a ⟹ a' : A ->
      Γ ⊢< Ax l > lift l A a ⟹ lift l A' a' : Lift l A

| ortho_lower : 
    ∀ Γ l A A' a a',
      Γ ⊢< Ax l > A ≡ A' : Sort l ->
      Γ ⊢< Ax l > a ⟹ a' : Lift l A ->
      Γ ⊢< l > lower l A a ⟹ lower l A' a' : A
      
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

| ortho_J_refl :
    ∀ Γ l i A a P p p' b e,
      Γ ⊢< Ax l > A : Sort l ->
      Γ ⊢< l > a ≡ b : A ->
      Γ ,, (l , A) ⊢< Ax i > P : Sort i ->
      Γ ⊢< i > p ⟹ p' : P <[a..] ->
      Γ ⊢< prop > e : Eq l A a b ->
      Γ ⊢< i > J l i A a P p b e ⟹ p' : P <[b..]

| ortho_lower_lift : 
    ∀ Γ n A1 A2 a a',
      Γ ⊢< Ax (ty n) > A1 ≡ A2 : Sort (ty n) ->
      Γ ⊢< ty n > a ⟹ a' : A1 ->
      Γ ⊢< ty n > lower (ty n) A1 (lift (ty n) A2 a) ⟹ a' : A1

| ortho_lift_lower : 
    ∀ Γ n A1 A2 a a',
      Γ ⊢< Ax (ty n) > A1 ≡ A2 : Sort (ty n) ->
      Γ ⊢< Ax (ty n) > a ⟹ a' : Lift (ty n) A1 ->
      Γ ⊢< Ax (ty n) > lift (ty n) A1 (lower (ty n) A2 a) ⟹ a' : Lift (ty n) A1

where "Γ ⊢< l > t ⟹ u : A" := (ortho_red Γ l t u A).

Derive Signature for ortho_red.


Reserved Notation "Γ ⊢s σ ⟹ τ : Δ" (at level 50, σ, τ, Δ at next level).

Inductive ortho_subst (Γ : ctx) : ctx -> (nat -> term) -> (nat -> term) -> Prop :=
  | ortho_sempty (σ σ' : nat -> term) :
    Γ ⊢s σ ⟹ σ' : ∙
  | ortho_scons (σ σ' : nat -> term) (Δ : ctx) l (A : term) :
    Γ ⊢s (↑ >> σ) ⟹ (↑ >> σ') : Δ ->
    Γ ⊢< l > σ var_zero ⟹ σ' var_zero : A <[↑ >> σ] ->
    Γ ⊢s σ ⟹ σ' : (Δ ,, (l , A))
where "Γ ⊢s σ ⟹ τ : Δ" := (ortho_subst Γ Δ σ τ).

Derive Signature for ortho_subst.


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
      ++ eapply conv_lam; eauto using validity_conv_right.
        1,2: eapply conv_refl; eauto using conv_ty_in_ctx_ty, conv_sym, validity_conv_right.
        eauto using conv_conv, conv_ty_in_ctx_conv.
      ++ eapply conv_pi; eauto using conv_sym, conv_ty_in_ctx_conv, validity_conv_right.
    + eapply conv_conv.
      eapply conv_beta; eauto using validity_conv_right, conv_ty_in_ctx_ty, type_conv.
      eapply subst_conv; eauto using conv_sym, validity_conv_ctx, substs_one.
  - eapply conv_trans. eapply conv_rec_succ; eauto using validity_conv_left.
    eapply subst_conv; eauto using validity_conv_ctx.
    2:rasimpl;reflexivity.
    eapply conv_scons_alt. eapply substs_one; eauto.
    eapply conv_rec; eauto using validity_conv_left.
  - eapply conv_trans. eapply conv_J_refl'; eauto using validity_conv_left.
    eapply conv_conv; eauto. eapply subst_conv; eauto using validity_ty_ctx, substs_one, conv_refl.
  - eapply conv_trans. 
    + eapply conv_lower. eapply conv_refl; eauto using validity_conv_left.
      eapply conv_conv. eapply conv_lift; eauto using conv_sym, conv_conv.
      eapply conv_Lift; eauto using conv_sym.
    + eapply conv_lower_lift; eauto using validity_conv_left, validity_conv_right.
  - eapply conv_trans. 
    + eapply conv_lift. eapply conv_refl; eauto using validity_conv_left.
      eapply conv_conv. eapply conv_lower; eauto using conv_sym, conv_conv, conv_Lift.
      eauto using conv_sym.
    + eapply conv_lift_lower; eauto using validity_conv_left, validity_conv_right.
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

Lemma ortho_subst_to_conv Γ σ τ Δ :
  Γ ⊢s σ ⟹ τ : Δ ->
  Γ ⊢s σ ≡ τ : Δ.
Proof.
  intros.
  induction H; eauto using ConvSubst.
  econstructor; eauto using ortho_to_conv.
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

  2,3,4,6,7,8,10,12,13,14,15:
    solve [ intros ; econstructor ;
            eauto 6 using WellRen_up, ctx_cons, ortho_validity_left, conv_ren,
              validity_conv_left, type_ren, type_nat ].

  2,3,4:
    solve [intros; cbn in *; eapply ortho_meta_conv ;
            [ ((eapply ortho_app + eapply ortho_rec + eapply ortho_J) ; try solve [ (eapply meta_conv_conv + eapply meta_conv + eapply ortho_meta_conv) ;
              [ eauto 13 using WellRen_up, WellRen_meta, ctx_typing, typing, ctx_cons, ortho_validity_left, conv_ren, validity_conv_left, type_ren, type_nat, ortho_meta_conv
              | rasimpl ; reflexivity]])
            | rasimpl; reflexivity]].

  3-8: solve [intros; cbn in *; eapply ortho_meta_conv2 ;
            [ ((eapply ortho_beta + eapply ortho_rec_zero + eapply ortho_rec_succ + eapply ortho_J_refl + eapply ortho_lower_lift + eapply ortho_lift_lower) ;
              try solve [ (eapply meta_conv_conv + eapply meta_conv + eapply ortho_meta_conv) ;
              [ eauto 12 using WellRen_up, ctx_cons, ortho_validity_left, conv_ren, validity_conv_left, type_ren, type_nat, ortho_meta_conv
              | ssimpl ; reflexivity]])
            | ssimpl; reflexivity | ssimpl; reflexivity ]].
  - econstructor; eauto using varty_ren.
  - intros. eapply ortho_irrel; eauto using type_ren.
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

Lemma ortho_subst_weak Γ Δ σ τ l A :
  Γ ⊢s σ ⟹ τ : Δ →
  Γ ⊢< Ax l > A : Sort l ->
  Γ ,, (l, A) ⊢s (σ >> ren_term S) ⟹ (τ >> ren_term S) : Δ.
Proof.
  induction 1 as [| σ τ Δ i B h ih ho] in l, A |- *.
  - constructor.
  - constructor.
    + auto.
    + eapply ortho_meta_conv.
      * unfold ">>". eapply ortho_ren. 1: eassumption.
        1:econstructor; eauto using validity_ty_ctx.
        eapply WellRen_S.
      * rasimpl. reflexivity.
Qed.

Lemma ortho_subst_up Γ Δ l A A' σ τ :
  Γ ⊢s σ ⟹ τ : Δ →
  A' = A <[ σ ] ->
  Γ ⊢< Ax l > A <[ σ ] : Sort l ->
  Γ ,, (l, A') ⊢s up_term σ ⟹ up_term τ : Δ ,, (l, A).
Proof.
  intros. subst.
  constructor.
  - eapply ortho_subst_weak; assumption.
  - rasimpl. cbn. econstructor.
    1: econstructor; eauto using validity_ty_ctx.
   eapply varty_meta.
    + constructor.
    + rasimpl. reflexivity.
Qed.


Theorem subst_ortho Γ l t u A σ τ Δ :
  Γ ⊢< l > t ⟹ u : A →
  ⊢ Δ →
  Δ ⊢s σ ⟹ τ : Γ →
  Δ ⊢< l > t <[σ] ⟹ u<[τ] : A<[σ].
Proof.
  intros. generalize Δ σ τ H0 H1. clear Δ σ τ H0 H1.
  induction H; intros; cbn.

  2,3,4,6,7,8,10,12,13,14,15:
    solve [ econstructor ;
            eauto 11 using ortho_subst_up, ctx_cons, ortho_validity_left, subst_conv,
              validity_conv_left, ortho_subst_to_conv,  refl_subst, validity_subst_conv_left  ].

  2,3,4:
    solve [eapply ortho_meta_conv ;
            [ ((eapply ortho_app + eapply ortho_rec + eapply ortho_J) ;
              try solve [ (eapply meta_conv_conv + eapply meta_conv + eapply ortho_meta_conv) ;
              [ eauto 20 using ctx_cons, ortho_validity_left, validity_conv_left, type_nat,
                ortho_subst_up, subst_conv, ortho_subst_to_conv
              | rasimpl ; reflexivity]])
            | rasimpl; reflexivity]].

  4,5:(assert (Δ,, (ty 0, Nat) ⊢< Ax l > P <[ up_term_term σ] : Sort l)
  by (eapply subst_ty; eauto using type_nat, ctx_cons, ortho_validity_left;
  eapply WellSubst_up; eauto using type_nat, ortho_subst_to_conv, validity_subst_conv_left)).

  - eapply subst_ortho_var; eauto.
  - eapply ortho_irrel.
    + eapply subst_ty; eauto using ortho_subst_to_conv, validity_subst_conv_left.
    + eapply type_conv. eapply subst_ty; eauto using ortho_subst_to_conv, validity_subst_conv_right, validity_ty_ctx.
      eapply subst_conv; eauto using validity_ty_ty, conv_refl, ortho_subst_to_conv, subst_sym, validity_ty_ctx.
  - eapply ortho_meta_conv2.
    eapply ortho_beta; eauto 14 using  ctx_cons, subst_conv, refl_subst,
      validity_conv_left, ortho_subst_to_conv, validity_subst_conv_left, ortho_subst_up.
    all:rasimpl;reflexivity.
  - eapply ortho_meta_conv2. eapply ortho_rec_zero; eauto.
    1: eapply ortho_meta_conv; eauto; rasimpl; reflexivity.
    2,3:rasimpl;reflexivity.
    eapply subst_ty; eauto using ctx_cons, type_nat.
    eapply WellSubst_up. eapply WellSubst_up.
    all:rasimpl; eauto using type_nat, ortho_subst_to_conv, validity_subst_conv_left.
  - eapply ortho_meta_conv2. eapply ortho_rec_succ; eauto.
    1-3:eapply ortho_meta_conv; eauto 8 using ctx_cons, type_nat, ortho_subst_up;  rasimpl; reflexivity.
    all:rasimpl;reflexivity.
  - eapply ortho_meta_conv.
    eapply ortho_J_refl; eauto 12 using ortho_subst_to_conv, validity_subst_conv_left,
      refl_subst, subst_conv, subst_ty, WellSubst_up, ctx_typing.
    eapply ortho_meta_conv; eauto.
    all:rasimpl;reflexivity.
  - eapply ortho_lower_lift; eauto using subst_conv, ortho_subst_to_conv, validity_subst_conv_left, refl_subst.
  - eapply ortho_lift_lower; eauto using subst_conv, ortho_subst_to_conv, validity_subst_conv_left, refl_subst.
Qed.

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
  - repeat destruct IHortho_red as (? & IHortho_red). subst.
    eauto 8 using conv_sym, conv_trans.
  - eapply type_inv in H. dependent destruction H.
    destruct l2; inversion lvl_eq.
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

  - repeat destruct IHortho_red as (? & IHortho_red).
    subst. rewrite H1 in *.
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
  - repeat destruct IHortho_red as (? & IHortho_red).
    subst. split; eauto. split; eauto using conv_sym, conv_trans.
  - split; eauto. split; eauto 8 using validity_conv_left, ortho_validity_left, subst_conv, substs_one, validity_conv_ctx, conv_refl.
    right. eauto 11.
Qed.

Lemma ortho_Eq_inv Γ l i A a b w T :
  Γ ⊢< l > Eq i A a b ⟹ w : T ->
  l = Ax prop /\
  Γ ⊢< Ax (Ax prop) > Sort prop ≡ T : Sort (Ax prop) /\
  exists A' a' b',
  Γ ⊢< Ax i > A ⟹ A' : Sort i /\
  Γ ⊢< i > a ⟹ a' : A /\
  Γ ⊢< i > b ⟹ b' : A /\
  w = Eq i A' a' b'.
Proof.
  intro.
  dependent induction H; eauto.
  - split; eauto. split; eauto 8 using conv_sort, validity_ty_ctx, ortho_validity_left.
  - repeat destruct IHortho_red as (? & IHortho_red).
    subst. split; eauto. split; eauto 9 using conv_sym, conv_trans.
  - eapply type_inv in H. dependent destruction H. inversion lvl_eq.
Qed.


Lemma ortho_J_inv Γ j l i A a P p b e w T :
  Γ ⊢< ty j > J l i A a P p b e ⟹ w : T ->
  ty j = i /\
  Γ ⊢< Ax i > P <[b..] ≡ T : Sort i /\
  ((exists A' a' P' p' b' e',
      Γ ⊢< Ax l > A ⟹ A' : Sort l /\
      Γ ⊢< l > a ⟹ a' : A /\
      Γ ,, (l , A) ⊢< Ax i > P ⟹ P' : Sort i /\
      Γ ⊢< i > p ⟹ p' : P <[a..] /\
      Γ ⊢< l > b ⟹ b' : A /\
      Γ ⊢< prop > e ⟹ e' : Eq l A a b /\
      w = J l i A' a' P' p' b' e')
  \/ (exists p',
      Γ ⊢< Ax l > A : Sort l /\
      Γ ⊢< l > a ≡ b : A /\
      Γ ,, (l , A) ⊢< Ax i > P : Sort i /\
      Γ ⊢< i > p ⟹ p' : P <[a..] /\
      Γ ⊢< prop > e : Eq l A a b /\
      w = p')).
Proof.
  intro.
  dependent induction H; eauto.
  - split; eauto. split. eapply conv_refl, subst_ty; eauto using ortho_validity_left, validity_ty_ctx, subst_one.
    left. eauto 15.
  - destruct IHortho_red as (eq & conv & disj). destruct disj as [K | K].
    all : repeat destruct K as (? & K).
    all:subst; split; eauto; split; eauto 9 using conv_sym, conv_trans.
    left. eauto 15.
  - split; eauto. split. eapply conv_refl, subst_ty; eauto using ortho_validity_left, validity_ty_ctx, subst_one, validity_conv_right.
    right. eauto 15.
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

Lemma ortho_Lift_inv Γ l i A w T :
  Γ ⊢< l > Lift i A ⟹ w : T ->
  l = Ax (Ax i) /\
  Γ ⊢< Ax (Ax (Ax i)) > Sort (Ax i) ≡ T : Sort (Ax (Ax i)) /\
  exists A',
  Γ ⊢< Ax i > A ⟹ A' : Sort i /\
  w = Lift i A'.
Proof.
  intro.
  dependent induction H; eauto.
  - split; eauto. split; eauto 8 using conv_sort, validity_ty_ctx, ortho_validity_left.
  - repeat destruct IHortho_red as (? & IHortho_red).
    subst. split; eauto. split; eauto 9 using conv_sym, conv_trans.
  - eapply type_inv in H. dependent destruction H. inversion lvl_eq.
Qed.

Lemma ortho_lift_inv Γ n i A a w T :
  Γ ⊢< ty n > lift i A a ⟹ w : T ->
  ty n = Ax i /\
  Γ ⊢< Ax (Ax i) > Lift i A ≡ T : Sort (Ax i) /\
  ((exists A' a',
   Γ ⊢< Ax i > A ≡ A' : Sort i /\
   Γ ⊢< i > a ⟹ a' : A /\
   w = lift i A' a') \/ 
  (exists A' b b' n ,
   i = ty n /\ 
   a = lower i A' b /\
   Γ ⊢< Ax i > A ≡ A' : Sort i /\ 
   Γ ⊢< Ax i > b ⟹ b' : Lift i A /\ 
   w = b')).
Proof.
  intro.
  dependent induction H; eauto.
  - split; eauto. split; eauto using conv_refl, type_Lift, validity_conv_left.
    left. eauto. 
  - repeat destruct IHortho_red as (? & IHortho_red).
    dependent destruction H1. split; eauto. split; eauto 9 using conv_sym, conv_trans.
  - split; eauto. split; eauto using conv_refl, type_Lift, validity_conv_left.
    right. eauto 10.
Qed.

Lemma ortho_lower_inv Γ n i A a w T :
  Γ ⊢< ty n > lower i A a ⟹ w : T ->
  ty n = i /\
  Γ ⊢< Ax i > A ≡ T : Sort i /\
  ((exists A' a',
   Γ ⊢< Ax i > A ≡ A' : Sort i /\
   Γ ⊢< Ax i > a ⟹ a' : Lift i A /\
   w = lower i A' a') \/ 
  (exists A' b b', 
   a = lift i A' b /\
   Γ ⊢< Ax i > A ≡ A' : Sort i /\ 
   Γ ⊢< i > b ⟹ b' : A /\ 
   w = b')).
Proof.
  intro.
  dependent induction H; eauto.
  - split; eauto. split; eauto using conv_refl, type_Lift, validity_conv_left.
    left. eauto.
  - repeat destruct IHortho_red as (? & IHortho_red).
    subst. split; eauto. split; eauto 9 using conv_sym, conv_trans.
  (* - eapply type_inv in H. dependent destruction H. inversion lvl_eq. *)
  - split; eauto. split; eauto using conv_refl, type_Lift, validity_conv_left.
    right. eauto 7.
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
    | Eq _ _ _ _ => eapply ortho_Eq_inv in h
    | J _ _ _ _ _ _ _ _ => eapply ortho_J_inv in h
    | Lift _ _ => eapply ortho_Lift_inv in h
    | lift _ _ _ => eapply ortho_lift_inv in h
    | lower _ _ _ => eapply ortho_lower_inv in h
    | _ => idtac
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
  | Eq _ A a b =>  1 + size A + size a + size b
  | J _ _ A a P p b e => 1 + size A + size a + size P + size p + size b + size e
  | Lift i A => 1 + size A 
  | lift i A a => 1 + size A + size a 
  | lower i A a => 1 + size A + size a
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
    ttinv t_red_t''. destruct t_red_t'' as (_ & t''_eq_n & _).
    subst.
    do 4 eexists. exists (var n). split; apply ortho_var; eauto.


  (* sort *)
  - ttinv t_red_t'. destruct t_red_t' as (t'_eq_sort & i_eq_ax).
    ttinv t_red_t''. destruct t_red_t'' as (t''_eq_sort & _).
    subst.
    do 4 eexists. exists (Sort l). split; apply ortho_sort; eauto.


  (* pi *)
  - rename t1 into A. rename t2 into B.
    ttinv t_red_t'. destruct t_red_t' as (A' & B' & t'_eq_pi & _ & A_red_A' & B_red_B' & _).
    ttinv t_red_t''. destruct t_red_t'' as (A'' & B'' & t''_eq_pi & _ & A_red_A'' & B_red_B'' & _).
    subst.

    destruct (IH A ltac:(simpl; lia) _ _ _ _ _ A_red_A' A_red_A'') as (A''' & A'_red_A''' & A''_red_A''').
    destruct (IH B ltac:(simpl; lia) _ _ _ _ _ B_red_B' B_red_B'') as (B''' & B'_red_B''' & B''_red_B''').
    do 4 eexists. exists (Pi l l0 A''' B''').
    split; apply ortho_pi; eauto 7 using conv_ty_in_ctx_ortho, ortho_to_conv, conv_refl, validity_ty_ty, validity_conv_left.

  (* lam *)
  - rename t1 into A. rename t2 into B. rename t3 into u.
    ttinv t_red_t'. destruct t_red_t' as (A' & B' & u' & _ & _ & t'_eq_lam & A_conv_A' & B_conv_B' & u_red_u').
    ttinv t_red_t''. destruct t_red_t'' as (A'' & B'' & u'' & _ & _ & t''_eq_lam & A_conv_A'' & B_conv_B'' & u_red_u'').
    subst.

    destruct (IH u ltac:(simpl; lia) _ _ _ _ _ u_red_u' u_red_u'') as (u''' & u'_red_u''' & u''_red_u''').

    do 4 eexists. exists (lam l l0 A B u''').
    split; apply ortho_lam; eauto using conv_ty_in_ctx_ortho, ortho_conv, conv_ty_in_ctx_conv, conv_sym.

  (* app *)
  - rename t1 into A. rename t2 into B. rename t3 into u. rename t4 into v.
    ttinv t_red_t'. ttinv t_red_t''.
    destruct t_red_t' as
      (i_eq & _ & [ (A' & B' & u' & v' & t'_eq & A_conv_A' & B_conv_B' & u_red_u' & v_red_v')
      | (A0 & B0 & w & w' & v' & u_eq & A_conv_A0 & B_conv_B0  & w_red_w' & v_red_v' & t'_eq) ]);
    destruct t_red_t'' as
      (_ & _ & [ (A'' & B'' & u'' & v'' & t''_eq & A_conv_A'' & B_conv_B'' & u_red_u'' & v_red_v'')
      | (A0_ & B0_ & w_ & w'' & v'' & u_eq_ & A_conv_A0_ & B_conv_B0_ & w_red_w'' & v_red_v'' & t''_eq) ]).

    all:subst.
    all:try destruct (IH u ltac:(simpl; lia) _ _ _ _ _ u_red_u' u_red_u'') as (u''' & u'_red_u''' & u''_red_u''').
    all:try destruct (IH v ltac:(simpl; lia) _ _ _ _ _ v_red_v' v_red_v'') as (v''' & v'_red_v''' & v''_red_v''').

    (* app-cong x app-cong *)
    + do 4 eexists. exists (app l (ty i) A B u''' v''').
    split; apply ortho_app; eauto using conv_sym, conv_ty_in_ctx_conv, conv_ty_in_ctx_ortho, conv_sym, ortho_conv, conv_pi, validity_conv_left.

    (* app-cong x beta *)
    + rename w_ into w. rename A0_ into A0.
      rename B0_ into B0. rename A_conv_A0_ into A_conv_A0. rename B_conv_B0_ into B_conv_B0.

      ttinv u_red_u'. destruct u_red_u' as (A0' & B0' & w' & _ & _ & u'_eq & A0_conv_A0' & B0_conv_B0' & w_red_w'). subst.

      rename w_red_w' into temp.
      assert (Γ,, (l, A) ⊢< ty i > w ⟹ w' : B) as w_red_w'. {eauto using conv_ty_in_ctx_ortho, conv_sym, ortho_conv. }
      clear temp.

      destruct (IH w ltac:(simpl; lia) _ _ _ _ _ w_red_w' w_red_w'') as (w''' & w'_red_w''' & w''_red_w''').

      do 4 eexists. exists (w''' <[ v''' ..]). split.
      ++ eapply ortho_beta; eauto 7 using conv_sym, conv_trans, ortho_conv, conv_ty_in_ctx_ortho, conv_ty_in_ctx_conv.
      ++ eauto using red_scons_id, subst_ortho.

    (* beta x app-cong *)
    (* roughly a copy-and-paste from the above *)
    + ttinv u_red_u''. destruct u_red_u'' as (A0'' & B0'' & w'' & _ & _ & u''_eq & A0_conv_A0'' & B0_conv_B0'' & w_red_w''). subst.

      rename w_red_w'' into temp.
      assert (Γ,, (l, A) ⊢< ty i > w ⟹ w'' : B) as w_red_w''. {eauto using conv_ty_in_ctx_ortho, conv_sym, ortho_conv. }
      clear temp.

      destruct (IH w ltac:(simpl; lia) _ _ _ _ _ w_red_w' w_red_w'') as (w''' & w'_red_w''' & w''_red_w''').

      do 4 eexists. exists (w''' <[ v''' ..]). split.
      ++ eauto using red_scons_id, subst_ortho.
      ++ eapply ortho_beta; eauto 7 using conv_sym, conv_trans, ortho_conv, conv_ty_in_ctx_ortho, conv_ty_in_ctx_conv.

    (* beta x beta *)
    + inversion u_eq_.  rewrite <- H2 in *. clear A_conv_A0_ B_conv_B0_ H0 H1 H2 u_eq_ w_ A0_ B0_.

      destruct (IH w ltac:(simpl; lia) _ _ _ _ _ w_red_w' w_red_w'') as (w''' & w'_red_w''' & w''_red_w''').

      do 4 eexists. exists (w''' <[ v''' .. ]).  split; eauto using subst_ortho, red_scons_id.


  (* Nat *)
  - ttinv t_red_t'. ttinv t_red_t''. subst.
    do 4 eexists. exists Nat. split; apply ortho_nat; eauto.

  (* zero *)
  - ttinv t_red_t'. ttinv t_red_t''. subst.
    do 4 eexists. exists zero. split; apply ortho_zero; eauto.

  (* succ *)
  - rename t into n.
    ttinv t_red_t'. destruct t_red_t' as (n' & t'_eq & n_red_n').
    ttinv t_red_t''. destruct t_red_t'' as (n'' & t''_eq & n_red_n'').
    subst.

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
      | (P'' & p_zero'' & p_succ'' & k & k'' & t''_eq & n_eq_ & P_red_P'' & p_zero_red_p_zero'' & p_succ_red_p_succ'' & k_red_k'')]].


    all:subst.

    all:try destruct (IH P ltac:(simpl; lia) _ _ _ _ _ P_red_P' P_red_P'') as (P''' & P'_red_P''' & P''_red_P''').
    all:try destruct (IH p_zero ltac:(simpl; lia) _ _ _ _ _ p_zero_red_p_zero' p_zero_red_p_zero'')
      as (p_zero''' & p_zero'_red_p_zero''' & p_zero''_red_p_zero''').
    all:try destruct (IH p_succ ltac:(simpl; lia) _ _ _ _ _ p_succ_red_p_succ' p_succ_red_p_succ'')
      as (p_succ''' & p_succ'_red_p_succ''' & p_succ''_red_p_succ''').

    (* rec x rec *)
    + destruct (IH n ltac:(simpl; lia) _ _ _ _ _ n_red_n' n_red_n'') as (n''' & n'_red_n''' & n''_red_n''').

      do 4 eexists. exists (rec l P''' p_zero''' p_succ''' n''').

      split; eapply ortho_rec;
      eauto 11 using ortho_conv, subst_conv, subst_one, type_zero, conv_ty_in_ctx_ortho, ortho_to_conv, subst_id_var1, ortho_validity_left, ctx_from_conv, refl_subst.

    (* rec x rec_zero *)
    + ttinv n_red_n'. subst.

      do 4 eexists. exists p_zero'''. split.
      2 : eauto.
      eapply ortho_rec_zero;
      eauto 12 using conv_ty_in_ctx_ortho, ortho_to_conv, subst_conv, ortho_conv, ortho_validity_left,
                ortho_validity_right, subst_id_var1, subst_one, type_zero, ctx_from_conv, refl_subst.

    (* rec x rec_succ *)
    + ttinv n_red_n'. destruct n_red_n' as (k' & n'_eq & k_red_k'). subst.
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
    + ttinv n_red_n''. subst.

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
    + ttinv n_red_n''. destruct n_red_n'' as (m'' & n''_eq & m_red_m''). subst.
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
    + inversion n_eq_. subst.
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

  (* Eq *)
  - rename t1 into A. rename t2 into a. rename t3 into b.
    ttinv t_red_t'. destruct t_red_t' as (l_eq & T_conv & A' & a' & b' & A_red_A' & a_red_a' & b_red_b' & eq).
    ttinv t_red_t''. destruct t_red_t'' as (l_eq' & T_conv' & A'' & a'' & b'' & A_red_A'' & a_red_a'' & b_red_b'' & eq').
    subst. dependent destruction l_eq. clear l_eq'.


    destruct (IH A ltac:(simpl; lia) _ _ _ _ _ A_red_A' A_red_A'') as (A''' & A'_red_A''' & A''_red_A''').
    destruct (IH a ltac:(simpl; lia) _ _ _ _ _ a_red_a' a_red_a'') as (a''' & a'_red_a''' & a''_red_a''').
    destruct (IH b ltac:(simpl; lia) _ _ _ _ _ b_red_b' b_red_b'') as (b''' & b'_red_b''' & b''_red_b''').

    do 5 eexists. split; eauto 6 using ortho_Eq, ortho_conv, ortho_to_conv.

  (* J *)
  - rename t1 into A. rename t2 into a. rename t3 into P. rename t4 into p. rename t5 into b. rename t6 into e.
    ttinv t_red_t'. destruct t_red_t' as (l_eq & T_conv & disj).
    ttinv t_red_t''. destruct t_red_t'' as (l_eq' & T_conv' & disj').
    subst. clear l_eq'.
    destruct disj as [(A' & a' & P' & p' & b' & e' & A_red_A' & a_red_a' & P_red_P' & p_red_p' & b_red_b' & e_red_e' & eq)
                      | (p' & AWt & a_conv_b & PWt & p_red_p' & eWt & eq)].
    all:destruct disj' as [(A'' & a'' & P'' & p'' & b'' & e'' & A_red_A'' & a_red_a'' & P_red_P'' & p_red_p'' & b_red_b'' & e_red_e'' & eq')
                      | (p'' & _ & a_conv_b' & _ & p_red_p'' & _ & eq')].
    all:subst.

    (* cong x cong *)
    + destruct (IH A ltac:(simpl; lia) _ _ _ _ _ A_red_A' A_red_A'') as (A''' & A'_red_A''' & A''_red_A''').
      destruct (IH a ltac:(simpl; lia) _ _ _ _ _ a_red_a' a_red_a'') as (a''' & a'_red_a''' & a''_red_a''').
      destruct (IH P ltac:(simpl; lia) _ _ _ _ _ P_red_P' P_red_P'') as (P''' & P'_red_P''' & P''_red_P''').
      destruct (IH p ltac:(simpl; lia) _ _ _ _ _ p_red_p' p_red_p'') as (p''' & p'_red_p''' & p''_red_p''').
      destruct (IH b ltac:(simpl; lia) _ _ _ _ _ b_red_b' b_red_b'') as (b''' & b'_red_b''' & b''_red_b''').
      destruct (IH e ltac:(simpl; lia) _ _ _ _ _ e_red_e' e_red_e'') as (e''' & e'_red_e''' & e''_red_e''').
      do 5 eexists.
      split; eapply ortho_J; eauto 6 using ortho_conv, ortho_to_conv, conv_ty_in_ctx_ortho, conv_Eq, subst_conv, substs_one.

    (* cong x red *)
    + destruct (IH p ltac:(simpl; lia) _ _ _ _ _ p_red_p' p_red_p'') as (p''' & p'_red_p''' & p''_red_p''').
      do 5 eexists. split; eauto.
      eapply ortho_J_refl; eauto 8 using ortho_validity_right, conv_ty_in_ctx_ortho, ortho_to_conv, conv_sym, conv_trans, conv_conv, subst_conv, substs_one, ortho_conv, conv_Eq.

    (* red x cong *)
    + destruct (IH p ltac:(simpl; lia) _ _ _ _ _ p_red_p' p_red_p'') as (p''' & p'_red_p''' & p''_red_p''').
      do 5 eexists. split; eauto.
      eapply ortho_J_refl; eauto 8 using ortho_validity_right, conv_ty_in_ctx_ortho, ortho_to_conv, conv_sym, conv_trans, conv_conv, subst_conv, substs_one, ortho_conv, conv_Eq.

    (* red x red *)
    + destruct (IH p ltac:(simpl; lia) _ _ _ _ _ p_red_p' p_red_p'') as (p''' & p'_red_p''' & p''_red_p''').
      do 5 eexists. split; eauto.

  (* Lift *)
  - rename t into A.
    ttinv t_red_t'. destruct t_red_t' as (l_eq & _ & A' & A_red_A' & t'_eq).
    ttinv t_red_t''. destruct t_red_t'' as (_ & _ & A'' & A_red_A'' & t''_eq). subst.

    destruct (IH A ltac:(simpl; lia) _ _ _ _ _ A_red_A' A_red_A'') as (A''' & A'_red_A''' & A''_red_A''').
    do 5 eexists. split; eauto using ortho_Lift.
  
  - rename t1 into A. rename t2 into a.
    ttinv t_red_t'. destruct t_red_t' as (l_eq & _ & disj). 
    ttinv t_red_t''. destruct t_red_t'' as (_ & _ & disj').
    dependent destruction l_eq.
    destruct disj as [ (A' & a' & A_eq_A' & a_red_a' & t'_eq) | (A' & b & b' & n & l_eq & a_eq & A_eq_A' & b_red_b' & t'_eq)];
    destruct disj' as [ (A'' & a'' & A_eq_A'' & a_red_a'' & t''_eq) | (A'' & b_ & b'' & n_ & l_eq_ & a_eq_ & A_eq_A'' & b_red_b'' & t''_eq_)]; subst.
    
    + destruct (IH a ltac:(simpl; lia) _ _ _ _ _ a_red_a' a_red_a'') as (a''' & a'_red_a''' & a''_red_a''').
      do 5 eexists. split; eapply ortho_lift; eauto using conv_sym, ortho_conv. 

    + rename n_ into n. rename b_ into b. ttinv a_red_a'. destruct a_red_a' as (_ & _ & disj).
      destruct disj as [ (A0 & b' & A''_eq_A0 & b_red_b' & a'_eq) | (A0 & d & d' & b_eq & A''_eq_A0 & d_red_d' & a'_eq) ]; subst.

      * eapply ortho_conv in b_red_b'. 2: eapply conv_Lift; eapply conv_sym, A_eq_A''.
        destruct (IH b ltac:(simpl; lia) _ _ _ _ _ b_red_b' b_red_b'') as (b''' & b'_red_b''' & b''_red_b''').
        do 5 eexists.
        split; eauto.
        eapply ortho_lift_lower; eauto using conv_sym, conv_trans, conv_Lift, ortho_conv.
        
      
      * assert (Γ ⊢< Ax (ty n) > lift (ty n) A0 d ⟹ lift (ty n) A' d' : Lift (ty n) A) as b_red_b'.
        { eapply ortho_conv. eapply ortho_lift; eauto using ortho_conv, conv_sym , conv_trans. eauto using conv_Lift, conv_sym, conv_trans. }
      
        destruct (IH (lift (ty n) A0 d) ltac:(simpl; lia) _ _ _ _ _ b_red_b' b_red_b'') as (b''' & b'_red_b''' & b''_red_b''').
        do 5 eexists. split; eauto.
    
    + ttinv a_red_a''. destruct a_red_a'' as (_ & _ & disj).
      destruct disj as [ (A0 & b'' & A'_eq_A0 & b_red_b'' & a'_eq) | (A0 & d & d'' & b_eq & A'_eq_A0 & d_red_d'' & a''_eq) ]; subst.

      * eapply ortho_conv in b_red_b''. 2: eapply conv_Lift; eapply conv_sym, A_eq_A'.
        destruct (IH b ltac:(simpl; lia) _ _ _ _ _ b_red_b' b_red_b'') as (b''' & b'_red_b''' & b''_red_b''').
        do 5 eexists.
        split; eauto.
        eapply ortho_lift_lower; eauto using conv_sym, conv_trans, conv_Lift, ortho_conv.
        
      
      * assert (Γ ⊢< Ax (ty n) > lift (ty n) A0 d ⟹ lift (ty n) A'' d'' : Lift (ty n) A) as b_red_b''.
        { eapply ortho_conv. eapply ortho_lift; eauto using ortho_conv, conv_sym , conv_trans. eauto using conv_Lift, conv_sym, conv_trans. }
      
        destruct (IH (lift (ty n) A0 d) ltac:(simpl; lia) _ _ _ _ _ b_red_b' b_red_b'') as (b''' & b'_red_b''' & b''_red_b''').
        do 5 eexists. split; eauto.

    + dependent destruction a_eq_. dependent destruction l_eq_.
      destruct (IH b ltac:(simpl; lia) _ _ _ _ _ b_red_b' b_red_b'') as (b''' & b'_red_b''' & b''_red_b''').
      do 5 eexists. split; eauto.

  - rename t1 into A. rename t2 into a.
    ttinv t_red_t'. destruct t_red_t' as (l_eq & _ & disj). 
    ttinv t_red_t''. destruct t_red_t'' as (_ & _ & disj'). subst.
    destruct disj as [ (A' & a' & A_eq_A' & a_red_a' & t'_eq) | (A' & b & b' & a_eq & A_eq_A' & b_red_b' & t'_eq)];
    destruct disj' as [ (A'' & a'' & A_eq_A'' & a_red_a'' & t''_eq) | (A'' & b_ & b'' & a_eq_ & A_eq_A'' & b_red_b'' & t''_eq_)]; subst.

    + destruct (IH a ltac:(simpl; lia) _ _ _ _ _ a_red_a' a_red_a'') as (a''' & a'_red_a''' & a''_red_a''').
      do 5 eexists. split; eapply ortho_lower; eauto using conv_sym, ortho_conv, conv_Lift.
    
    + rename b_ into b. ttinv a_red_a'. destruct a_red_a' as (_ & _ & disj).
      destruct disj as [ (A0 & b' & A''_eq_A0 & b_red_b' & a'_eq) | (A0 & d & d' & n & lvl_eq & b_eq & A''_eq_A0 & d_red_d' & a'_eq)]; subst.

      * eapply ortho_conv in b_red_b'. 2:eapply conv_sym, A_eq_A''. 
        destruct (IH b ltac:(simpl; lia) _ _ _ _ _ b_red_b' b_red_b'') as (b''' & b'_red_b''' & b''_red_b''').
        do 5 eexists.
        split; eauto.
        eapply ortho_lower_lift; eauto using conv_sym, conv_trans, conv_Lift, ortho_conv.

      * assert (Γ ⊢< ty i > lower (ty i) A0 d ⟹ lower (ty i) A' d' : A) as b_red_b'.
        { eapply ortho_conv. eapply ortho_lower; eauto using ortho_conv, conv_sym , conv_trans, conv_Lift. eauto using conv_sym, conv_trans. }

        destruct (IH (lower (ty i) A0 d) ltac:(simpl; lia) _ _ _ _ _ b_red_b' b_red_b'') as (b''' & b'_red_b''' & b''_red_b''').
        do 5 eexists. split; eauto.
      
    + ttinv a_red_a''. destruct a_red_a'' as (_ & _ & disj).
      destruct disj as [ (A0 & b'' & A'_eq_A0 & b_red_b'' & a''_eq) | (A0 & d & d'' & n & lvl_eq & b_eq & A'_eq_A0 & d_red_d'' & a''_eq)]; subst.

      * eapply ortho_conv in b_red_b''. 2:eapply conv_sym, A_eq_A'. 
        destruct (IH b ltac:(simpl; lia) _ _ _ _ _ b_red_b' b_red_b'') as (b''' & b'_red_b''' & b''_red_b''').
        do 5 eexists.
        split; eauto.
        eapply ortho_lower_lift; eauto using conv_sym, conv_trans, conv_Lift, ortho_conv.

      * assert (Γ ⊢< ty i > lower (ty i) A0 d ⟹ lower (ty i) A'' d'' : A) as b_red_b''.
        { eapply ortho_conv. eapply ortho_lower; eauto using ortho_conv, conv_sym , conv_trans, conv_Lift. eauto using conv_sym, conv_trans. }

        destruct (IH (lower (ty i) A0 d) ltac:(simpl; lia) _ _ _ _ _ b_red_b' b_red_b'') as (b''' & b'_red_b''' & b''_red_b''').
        do 5 eexists. split; eauto.

    + dependent destruction a_eq. rename b_ into b.
      destruct (IH b ltac:(simpl; lia) _ _ _ _ _ b_red_b' b_red_b'') as (b''' & b'_red_b''' & b''_red_b''').
      do 5 eexists. split; eauto.
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

Derive Signature for ortho_redd.

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
  Going from the original untyped version to this typed one took me a lot of trial and error.
  
  Important: We cannot ask that Δ ⊢< i > t : A -> Γ ⊢< l > f t : P t, because the contexts f, P
  might constraint t to be of a certain form, like
    f t := refl t
    P t := Eq Nat 0 t
  But we need at least to ensure that, for t and u convertible, f and P are defined for t iff 
  f and P are defined for u. Indeed, we need to avoid evil contexts like 
    f t := match t with | zero => v | _ => w end
  which do not respect conversion.
  *)
Lemma equiv_red_ind {Γ Δ l A i} P f :
    (forall t u, Δ ⊢< i > t ≡ u : A -> Γ ⊢< l > f t : P t -> Γ ⊢< l > f u : P u) ->
    (forall t u, Δ ⊢< i > t ⟹ u : A -> Γ ⊢< l > f t : P t -> Γ ⊢< l > f t ≈ f u : P t) ->
    forall {t u}, Δ ⊢< i > t ≈ u : A -> Γ ⊢< l > f t : P t -> Γ ⊢< l > f t ≈ f u : P t.
Proof.
  intros. induction H1.
  - eapply H0; eauto.
  - eapply equiv_to_conv in H1_ as H1'. 
    eapply H in H1'; eauto.
    eapply IHortho_equiv1 in H2.
    eapply IHortho_equiv2 in H1'.
    eapply equiv_trans. 1:eassumption.
    eapply equiv_conv. 1:eassumption.
    eapply equiv_to_conv in H2, H1'.
    eauto using type_unicity, validity_conv_left, validity_conv_right.
  - eapply equiv_to_conv in H1 as H1'.
    eapply conv_sym in H1'.
    eapply H in H1'; eauto.
    eapply IHortho_equiv in H1'.
    eapply equiv_sym. 
    eapply equiv_conv; eauto.
    eapply equiv_to_conv, validity_conv_right in H1'.
    eauto using type_unicity.
Qed.

Lemma equiv_pi Γ i j A B A' B' :
      Γ ⊢< Ax i > A ≈ A' : Sort i →
      Γ ,, (i , A) ⊢< Ax j > B ≈ B' : Sort j →
      Γ ⊢< Ax (Ru i j) > Pi i j A B ≈ Pi i j A' B' : Sort (Ru i j).
Proof.
  intros A_equiv_A' B_equiv_B'.
  eapply equiv_trans.
  - refine (equiv_red_ind (fun _ => Sort (Ru i j)) (fun B => Pi i j A B) _ _ B_equiv_B' _).
    3 : eauto 6 using type_pi, equiv_to_conv, validity_conv_left.
    + intros. eauto using type_pi, equiv_to_conv, validity_conv_left, validity_conv_right.
    + intros. apply equiv_step. eauto using ortho_pi, equiv_to_conv, validity_conv_left, ortho_refl.
  - refine (equiv_red_ind (fun _ => Sort (Ru i j)) (fun A => Pi i j A B') _ _ A_equiv_A' _).
    3 : eauto 6 using type_pi, equiv_to_conv, validity_conv_left, validity_conv_right.
    + intros; apply type_inv in H0; dependent destruction H0;
      eauto using type_pi, validity_conv_right, validity_conv_left, conv_sym, conv_ty_in_ctx_ty.
    + intros v v' v_red_v' Wt. apply type_inv in Wt. dependent destruction Wt.
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
    + intros; eauto using type_lam, validity_conv_left, validity_conv_right.
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
    + intros. eauto 7 using equiv_to_conv, validity_conv_left, validity_conv_right, type_app.
    + intros. apply equiv_step.
      eauto 9 using ortho_app, equiv_to_conv, validity_conv_left, ortho_refl, conv_refl.
  - refine (equiv_red_ind (fun u => B <[ u ..]) (fun u => app i j A B t' u) _ _ H2 _).
    3:eauto 8 using type_app, equiv_to_conv, validity_conv_left, validity_conv_right.
    + intros. eauto 7 using type_app, validity_conv_left, equiv_to_conv, validity_conv_right.
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
  - intros. eauto using type_succ, validity_conv_left, validity_conv_right.
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
    + intros. eauto 9 using type_rec, equiv_to_conv, validity_conv_left, validity_conv_right.
    + intros. apply equiv_step. eauto 12 using ortho_rec, equiv_to_conv, validity_conv_left, ortho_refl.
  - refine (equiv_red_ind (fun _ => P <[ t.. ]) (fun p_succ => rec l P p_zero' p_succ t) _ _ p_succ_equiv_p_succ' _).
    3: eauto 10 using type_rec, equiv_to_conv, validity_conv_left, validity_conv_right.
    + intros. eauto 9 using type_rec, equiv_to_conv, validity_conv_left, validity_conv_right.
    + intros. apply equiv_step.
      eauto 12 using ortho_rec, equiv_to_conv, validity_conv_left, validity_conv_right, ortho_refl.
  - refine (equiv_red_ind (fun t => P <[ t.. ]) (fun t => rec l P p_zero' p_succ' t) _ _ t_equiv_t' _).
    3 : eauto 10 using type_rec, equiv_to_conv, validity_conv_left, validity_conv_right.
    + intros. eauto 9 using type_rec, equiv_to_conv, validity_conv_left, validity_conv_right.
    + intros. apply equiv_step.
      eauto 12 using ortho_rec, equiv_to_conv, validity_conv_left, validity_conv_right, ortho_refl.
  - eapply (equiv_conv _ _ (P <[ t'..])).
    2: eapply subst_conv; eauto using substs_one, equiv_to_conv, validity_conv_ctx, validity_conv_left, conv_refl, conv_sym.
    refine (equiv_red_ind (fun P => P <[ t'.. ]) (fun P => rec l P p_zero' p_succ' t') _ _ P_equiv_P' _).
    3 : eauto 10 using type_rec, equiv_to_conv, validity_conv_left, validity_conv_right.
    + intros; apply type_inv in H0; dependent destruction H0.
      apply type_rec; eauto 9 using equiv_to_conv, subst_conv, type_conv, type_zero,
        subst_one, validity_ty_ctx, validity_conv_left, conv_sym, conv_ty_in_ctx_ty, subst_id_var1, ctx_from_conv, refl_subst.
    + intros v v' v_red_v' Wt.
      apply type_inv in Wt. dependent destruction Wt.
      apply equiv_step. eauto using ortho_refl, ortho_rec.
Qed.

Lemma equiv_Eq Γ l A A' a a' b b' :
  Γ ⊢< Ax l > A ≈ A' : Sort l ->
  Γ ⊢< l > a ≈ a' : A ->
  Γ ⊢< l > b ≈ b' : A ->
  Γ ⊢< Ax prop > Eq l A a b ≈ Eq l A' a' b' : Sort prop.
Proof.
  intros A_equiv_A' a_equiv_a' b_equiv_b'.
  eapply equiv_trans. eapply equiv_trans.
  - refine (equiv_red_ind (fun _ => Sort prop) (fun b => Eq l A a b) _ _ b_equiv_b' _).
    3:eauto 8 using type_Eq, equiv_to_conv, validity_conv_left.
    + intros. eauto 11 using type_Eq, equiv_to_conv, validity_conv_left, validity_conv_right.
    + intros. apply equiv_step.
      eauto 12 using ortho_Eq, equiv_to_conv, validity_conv_left, validity_conv_right, ortho_refl.
  - refine (equiv_red_ind (fun _ => Sort prop) (fun a => Eq l A a b') _ _ a_equiv_a' _).
    3:eauto 8 using type_Eq, equiv_to_conv, validity_conv_left, validity_conv_right.
    + intros. eauto 11 using type_Eq, equiv_to_conv, validity_conv_left, validity_conv_right.
    + intros. apply equiv_step.
      eauto 12 using ortho_Eq, equiv_to_conv, validity_conv_left, validity_conv_right, ortho_refl.
  - refine (equiv_red_ind (fun _ => Sort prop) (fun A => Eq l A _ _) _ _ A_equiv_A' _).
    3:eauto 8 using type_Eq, equiv_to_conv, validity_conv_left, validity_conv_right.
    + intros.
      eapply type_inv in H0; dependent destruction H0;
      eauto 7 using type_Eq, validity_conv_left, type_conv, conv_sym.
    + intros. apply equiv_step.
      eapply type_inv in H0. dependent destruction H0.
      eapply ortho_Eq; eauto using ortho_refl.
Qed.

Lemma equiv_J Γ l i A A' a a' P P' p p' b b' e e' :
  Γ ⊢< Ax l > A ≈ A' : Sort l ->
  Γ ⊢< l > a ≈ a' : A ->
  Γ ,, (l , A) ⊢< Ax i > P ≈ P' : Sort i ->
  Γ ⊢< i > p ≈ p' : P <[a..] ->
  Γ ⊢< l > b ≈ b' : A ->
  Γ ⊢< prop > e ≈ e' : Eq l A a b ->
  Γ ⊢< i > J l i A a P p b e ≈ J l i A' a' P' p' b' e' : P <[b..].
Proof.
  intros A_equiv_A' a_equiv_a' P_equiv_P' p_equiv_p' b_equiv_b' e_equiv_e'.
  eapply equiv_trans. eapply equiv_trans. eapply equiv_trans. eapply equiv_trans. eapply equiv_trans.
  - refine (equiv_red_ind _ (fun a => J l i A a P p b e) _ _ a_equiv_a' _).
    3:eapply type_J; eauto using equiv_to_conv, validity_conv_left.
    + intros.
      eapply type_inv in H0; dependent destruction H0.
      eapply type_J; eauto 9 using equiv_to_conv, validity_conv_left,
      validity_conv_right, conv_Eq, type_conv, conv_refl, subst_conv, substs_one, validity_ty_ctx, conv_sym.
    + intros. apply equiv_step.
      eapply type_inv in H0. dependent destruction H0.
      eapply ortho_J; eauto using ortho_refl.
  - refine (equiv_red_ind _ (fun e => J l i A _ P p b e) _ _ e_equiv_e' _).
    3:eapply type_J; eauto 13 using equiv_to_conv, validity_conv_left, validity_conv_right,
        type_conv, conv_Eq, conv_refl, substs_one, validity_ty_ctx, subst_conv.
    + intros. eapply type_inv in H0; dependent destruction H0.
      eapply type_J; eauto 9 using equiv_to_conv, validity_conv_left,
      validity_conv_right, conv_Eq, type_conv, conv_refl, subst_conv, substs_one, validity_ty_ctx, conv_sym.
    + intros. apply equiv_step.
      eapply type_inv in H0. dependent destruction H0.
      eapply ortho_J; eauto 6 using ortho_refl, ortho_conv, conv_Eq, conv_refl, equiv_to_conv.
  - refine (equiv_red_ind _ (fun p => J l i A _ P p b _) _ _ p_equiv_p' _).
    3:eapply type_J; eauto 13 using equiv_to_conv, validity_conv_left, validity_conv_right,
        type_conv, conv_Eq, conv_refl, substs_one, validity_ty_ctx, subst_conv.
    + intros. 
      eapply type_inv in H0; dependent destruction H0.
      eapply type_J; eauto 9 using equiv_to_conv, validity_conv_left,
      validity_conv_right, conv_Eq, type_conv, conv_refl, subst_conv, substs_one, validity_ty_ctx, conv_sym.
    + intros. apply equiv_step.
      eapply type_inv in H0. dependent destruction H0.
      eapply ortho_J; eauto 7 using ortho_refl, ortho_conv, conv_Eq, conv_refl, equiv_to_conv,
        substs_one, validity_conv_left, validity_ty_ctx, subst_conv.
  - refine (equiv_red_ind (fun b => P<[b..]) (fun b => J l i A _ P _ b _) _ _ b_equiv_b' _).
    3:eapply type_J; eauto 13 using equiv_to_conv, validity_conv_left, validity_conv_right,
        type_conv, conv_Eq, conv_refl, substs_one, validity_ty_ctx, subst_conv.
    + intros. 
      eapply type_inv in H0; dependent destruction H0.
      eapply type_J; eauto 9 using equiv_to_conv, validity_conv_left,
      validity_conv_right, conv_Eq, type_conv, conv_refl, subst_conv, substs_one, validity_ty_ctx, conv_sym.
    + intros. apply equiv_step.
      eapply type_inv in H0. dependent destruction H0.
      eapply ortho_J; eauto 7 using ortho_refl, ortho_conv, conv_Eq, conv_refl, equiv_to_conv,
        substs_one, validity_conv_left, validity_ty_ctx, subst_conv.
  - refine (equiv_red_ind _ (fun A => J l i A _ P _ _ _) _ _ A_equiv_A' _).
    3:eapply type_conv.
    3:eapply type_J; eauto 13 using equiv_to_conv, validity_conv_left, validity_conv_right,
        type_conv, conv_Eq, conv_refl, substs_one, validity_ty_ctx, subst_conv.
    3:eauto 11 using equiv_to_conv, validity_conv_left, subst_conv, substs_one, conv_sym, validity_ty_ctx, conv_refl.
    + intros. eapply type_inv in H0; dependent destruction H0.
      eapply type_conv.
      1:eapply type_J; eauto 9 using equiv_to_conv, validity_conv_left,
      validity_conv_right, conv_Eq, type_conv, conv_refl, subst_conv, substs_one, validity_ty_ctx, conv_sym, conv_ty_in_ctx_ty.
      eauto 11 using equiv_to_conv, validity_conv_left, subst_conv, substs_one, conv_sym, validity_ty_ctx, conv_refl.
    + intros. apply equiv_step.
      eapply type_inv in H0. dependent destruction H0.
      eapply ortho_conv.
      eapply ortho_J; eauto 7 using ortho_refl, ortho_conv, conv_Eq, conv_refl, equiv_to_conv,
        substs_one, validity_conv_left, validity_ty_ctx, subst_conv.
      eauto 11 using equiv_to_conv, validity_conv_left, subst_conv, substs_one, conv_sym, validity_ty_ctx, conv_refl.
  - refine (equiv_red_ind (fun P => P<[b..]) (fun P => J l i _ _ P _ _ _) _ _ P_equiv_P' _).
    3:eapply type_conv.
    3:eapply type_J; eauto 13 using equiv_to_conv, validity_conv_left, validity_conv_right,
        type_conv, conv_Eq, conv_refl, substs_one, validity_ty_ctx, subst_conv, conv_ty_in_ctx_ty.
    3:eauto 11 using equiv_to_conv, validity_conv_left, subst_conv, substs_one, conv_sym, validity_ty_ctx, conv_refl.
    + intros. eapply type_inv in H0; dependent destruction H0.
      eapply type_conv.
      1:eapply type_J; eauto 9 using equiv_to_conv, validity_conv_left,
      validity_conv_right, conv_Eq, type_conv, conv_refl, subst_conv, substs_one, validity_ty_ctx, conv_sym, conv_ty_in_ctx_ty.
      eauto 11 using equiv_to_conv, validity_conv_left, subst_conv, substs_one, conv_sym, validity_ty_ctx, conv_refl.
    + intros. apply equiv_step.
      eapply type_inv in H0. dependent destruction H0.
      eapply ortho_conv.
      eapply ortho_J; eauto 7 using ortho_refl, ortho_conv, conv_Eq, conv_refl, equiv_to_conv,
        substs_one, validity_conv_left, validity_ty_ctx, subst_conv, conv_ty_in_ctx_ortho.
      eapply subst_conv; eauto 10 using substs_one, equiv_to_conv, validity_ty_ctx, conv_sym, validity_conv_left, conv_refl, ortho_to_conv.
Qed.

Lemma equiv_Lift Γ l A A' : 
  Γ ⊢< Ax l > A ≈ A' : Sort l ->
  Γ ⊢< Ax (Ax l) > Lift l A ≈ Lift l A' : Sort (Ax l).
Proof.
  intros A_equiv_A'. refine (equiv_red_ind _ (fun A => Lift l A) _ _ A_equiv_A' _).
  3:eauto 8 using type_Lift, equiv_to_conv, validity_conv_left.
  + intros. eauto 11 using type_Lift, equiv_to_conv, validity_conv_left, validity_conv_right.
  + intros. apply equiv_step.
    eauto 12 using ortho_Lift, equiv_to_conv, validity_conv_left, validity_conv_right, ortho_refl.
Qed.

Lemma equiv_lift Γ l A A' a a' : 
  Γ ⊢< Ax l > A ≈ A' : Sort l ->
  Γ ⊢< l > a ≈ a' : A ->
  Γ ⊢< Ax l > lift l A a ≈ lift l A' a' : Lift l A.
Proof.
  intros A_equiv_A' a_equiv_a'. eapply equiv_trans.
  - refine (equiv_red_ind _ (fun a => lift l A a) _ _ a_equiv_a' _).
    3:eauto 8 using type_lift, equiv_to_conv, validity_conv_left.
    + intros. eauto 11 using type_lift, equiv_to_conv, validity_conv_left, validity_conv_right.
    + intros. apply equiv_step. eapply type_inv in H0. dependent destruction H0.
      eauto 12 using ortho_lift, equiv_to_conv, validity_conv_left, validity_conv_right, ortho_refl, conv_refl.
  - refine (equiv_red_ind (fun A => Lift _ A) (fun A => lift l A _) _ _ A_equiv_A' _).
    3:eauto 8 using type_lift, equiv_to_conv, validity_conv_left, validity_conv_right.
    + intros. eapply type_inv in H0; dependent destruction H0.
      eapply type_lift; eauto; eauto using validity_conv_left, validity_conv_right, type_conv, conv_sym.
    + intros. apply equiv_step. eapply type_inv in H0. dependent destruction H0.
      eapply ortho_lift; eauto using ortho_refl, ortho_to_conv.
Qed.
  

Lemma equiv_lower Γ l A A' a a' : 
  Γ ⊢< Ax l > A ≈ A' : Sort l ->
  Γ ⊢< Ax l > a ≈ a' : Lift l A ->
  Γ ⊢< l > lower l A a ≈ lower l A' a' : A.
Proof.
  intros A_equiv_A' a_equiv_a'. eapply equiv_trans.
  - refine (equiv_red_ind _ (fun a => lower l A a) _ _ a_equiv_a' _).
    3:eauto 8 using type_lower, equiv_to_conv, validity_conv_left.
    + intros. eauto 11 using type_lower, equiv_to_conv, validity_conv_left, validity_conv_right.
    + intros. apply equiv_step. eapply type_inv in H0. dependent destruction H0.
      eauto 12 using ortho_lower, equiv_to_conv, validity_conv_left, validity_conv_right, ortho_refl, conv_refl.
  - refine (equiv_red_ind (fun A => A) (fun A => lower l A _) _ _ A_equiv_A' _).
    3:eauto 8 using type_lower, equiv_to_conv, validity_conv_left, validity_conv_right.
    + intros. eapply type_inv in H0; dependent destruction H0.
      eapply type_lower; eauto; eauto using validity_conv_left, validity_conv_right, type_conv, conv_sym, conv_Lift.
    + intros. apply equiv_step. eapply type_inv in H0. dependent destruction H0.
      eapply ortho_lower; eauto using ortho_refl, ortho_to_conv.
Qed.

Lemma conv_to_equiv Γ l t u A :
  Γ ⊢< l > t ≡ u : A -> Γ ⊢< l > t ≈ u : A.
Proof.
  intro H. induction H.
  all : try solve [apply equiv_step; econstructor; eauto using conv_refl, ortho_refl ].
  all : eauto using equiv_pi, equiv_lam, equiv_app, equiv_succ,
    equiv_rec, equiv_conv, equiv_sym, equiv_trans, equiv_Eq, equiv_J, equiv_Lift, equiv_lower, equiv_lift.
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
  - destruct IHpi_red_T1 as (A'' & B'' & v_eq & A_red & B_red). subst.
    destruct (IHpi_red_T2 l1 l2 A'' B'' _ eq_refl) as (A''' & B''' & u_eq & A''_red & B''_red). subst.
    exists A'''. exists B'''. repeat split.
    all : (eapply redd_trans; eauto).
    + apply redd_to_conv in A_red. eapply (redd_conv_in_ctx (Γ ,, (l1, A'')));
      eauto 6 using conv_ccons, ctx_conv_refl, conv_sym, validity_conv_left, validity_ty_ctx.
Qed.

Lemma Lift_redd Γ l l' A t T :
  Γ ⊢< l' > Lift l A ⟹* t : T ->
  exists A', 
    t = Lift l A' /\ Γ ⊢< Ax l > A ⟹* A' : Sort l.
Proof.
  intro lift_redd_t.
  dependent induction lift_redd_t.
  - ttinv H. destruct H as (l'_eq & conv_ty & A' & A_red_A' & u_eq). subst.
    exists A'. split; eauto using redd_step.
  - destruct IHlift_redd_t1 as (A' & eq & A_redd_A'). subst.  
    edestruct IHlift_redd_t2 as (A'' & eq & A'_redd_A''); eauto. subst.
    exists A''. split; eauto using redd_trans.
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
  destruct Pi_red_2 as (A1 & B1 & v_eq_ & A'_redd_A1 & B'_redd_B1). subst.
  dependent destruction v_eq_.
  apply redd_to_conv in A_redd_A0, B_redd_B0, A'_redd_A1, B'_redd_B1.
  split; split; split; auto.
  - eauto using conv_trans, conv_sym.
  - eapply conv_trans. apply B_redd_B0. eauto using conv_ty_in_ctx_conv, conv_sym.
Qed.

Corollary Lift_inj Γ l i A i' A' T :
  Γ ⊢< l > Lift i A ≡ Lift i' A' : T ->
  i = i' /\ Γ ⊢< Ax i > A ≡ A' : Sort i.
Proof.
  intro Lift_eq.
  apply CR in Lift_eq.
  destruct Lift_eq as (v & Lift_red_1 & Lift_red_2).
  apply Lift_redd in Lift_red_1.
  destruct Lift_red_1 as (A0 & v_eq & A_red_A0).
  apply Lift_redd in Lift_red_2.
  destruct Lift_red_2 as (A1 & v_eq_ & A_red_A1).
  subst. dependent destruction v_eq_.
  split; eauto using redd_to_conv, conv_sym, conv_trans.
Qed.

Proposition sort_neq_nat Γ l l' T :
  Γ ⊢< l' > Sort l ≡ Nat : T -> False.
Proof.
  intro sort_eq_nat.
  apply CR in sort_eq_nat.
  destruct sort_eq_nat as (t & sort_redd_t & nat_redd_t).
  apply sort_redd in sort_redd_t.
  apply nat_redd in nat_redd_t. subst.
  inversion nat_redd_t.
Qed.

Proposition sort_neq_pi Γ l l' i j A B T :
  Γ ⊢< l' > Sort l ≡ Pi i j A B : T -> False.
Proof.
  intro sort_eq_pi.
  apply CR in sort_eq_pi.
  destruct sort_eq_pi as (t & sort_redd_t & pi_redd_t).
  apply sort_redd in sort_redd_t.
  apply pi_redd in pi_redd_t as (A' & B' & H & _). subst.
  inversion H.
Qed.

Proposition nat_neq_pi Γ l' i j A B T :
  Γ ⊢< l' > Nat ≡ Pi i j A B : T -> False.
Proof.
  intro nat_eq_pi.
  apply CR in nat_eq_pi.
  destruct nat_eq_pi as (t & nat_redd_t & pi_redd_t).
  apply nat_redd in nat_redd_t.
  apply pi_redd in pi_redd_t as (A' & B' & H & _). subst.
  inversion H.
Qed.

Proposition Lift_neq_nat Γ l A l' T :
  Γ ⊢< l' > Lift l A ≡ Nat : T -> False.
Proof.
  intro Lift_eq_nat.
  apply CR in Lift_eq_nat.
  destruct Lift_eq_nat as (t & Lift_redd_t & nat_redd_t).
  apply Lift_redd in Lift_redd_t as (A' & eq & _).
  apply nat_redd in nat_redd_t. subst.
  inversion nat_redd_t.
Qed.

Proposition Lift_neq_pi Γ l l' i j A B A0 T :
  Γ ⊢< l' > Lift l A0 ≡ Pi i j A B : T -> False.
Proof.
  intro Lift_eq_pi.
  apply CR in Lift_eq_pi.
  destruct Lift_eq_pi as (t & Lift_redd_t & pi_redd_t).
  apply Lift_redd in Lift_redd_t as (A0' & eq & _).
  apply pi_redd in pi_redd_t as (A' & B' & H & _). subst.
  inversion H.
Qed.

Proposition sort_neq_Lift Γ l l' A l'' T :
  Γ ⊢< l' > Sort l ≡ Lift l'' A : T -> False.
Proof.
  intro sort_eq_Lift.
  apply CR in sort_eq_Lift.
  destruct sort_eq_Lift as (t & sort_redd_t & Lift_redd_t).
  apply sort_redd in sort_redd_t.
  apply Lift_redd in Lift_redd_t as (A0' & eq & _). subst.
  inversion eq.
Qed.

