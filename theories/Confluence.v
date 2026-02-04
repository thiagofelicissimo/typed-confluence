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



| ortho_sigma :
    ∀ Γ n m A B A' B',
      Γ ⊢< Ax (ty n) > A ⟹ A' : Sort (ty n) →
      Γ ,, (ty n , A) ⊢< Ax (ty m) > B ⟹ B' : Sort (ty m) →
      Γ ⊢< Ax (ty (max n m)) > Sigma (ty n) (ty m) A B ⟹ Sigma (ty n) (ty m) A' B' : Sort (ty (max n m))

| ortho_pair :
    ∀ Γ n m A B a b A' B' a' b',
      Γ ⊢< Ax (ty n) > A ≡ A' : Sort (ty n) →
      Γ ,, (ty n , A) ⊢< Ax (ty m) > B ≡ B' : Sort (ty m) →
      Γ ⊢< ty n > a ⟹ a' : A →
      Γ ⊢< ty m > b ⟹ b' : B <[a..] →
      Γ ⊢< ty (max n m) > pair (ty n) (ty m) A B a b ⟹ pair (ty n) (ty m) A' B' a' b' : Sigma (ty n) (ty m) A B

| ortho_pi1 :
    ∀ Γ n m A B t A' B' t',
      Γ ⊢< Ax (ty n) > A ≡ A' : Sort (ty n) →
      Γ ,, (ty n , A) ⊢< Ax (ty m) > B ≡ B' : Sort (ty m) →
      Γ ⊢< ty (max n m) > t ⟹ t' : Sigma (ty n) (ty m) A B →
      Γ ⊢< ty n > pi1 (ty n) (ty m) A B t ⟹ pi1 (ty n) (ty m) A' B' t' : A

| ortho_pi2 :
    ∀ Γ n m A B t A' B' t',
      Γ ⊢< Ax (ty n) > A ≡ A' : Sort (ty n) →
      Γ ,, (ty n , A) ⊢< Ax (ty m) > B ≡ B' : Sort (ty m) →
      Γ ⊢< ty (max n m) > t ⟹ t' : Sigma (ty n) (ty m) A B →
      Γ ⊢< ty m > pi2 (ty n) (ty m) A B t ⟹ pi2 (ty n) (ty m) A' B' t' : B <[(pi1 (ty n) (ty m) A B t)..]

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

| ortho_cast :
    ∀ Γ i A A' B B' e e' a a',
      Γ ⊢< Ax i > A ⟹ A' : Sort i ->
      Γ ⊢< Ax i > B ⟹ B' : Sort i ->
      Γ ⊢< prop > e ⟹ e' : Eq (Ax i) (Sort i) A B ->
      Γ ⊢< i > a ⟹ a' : A ->
      Γ ⊢< i > cast i A B e a ⟹ cast i A' B' e' a' : B      
        
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

| ortho_pi1pair : 
    ∀ Γ n m A B A' B' a b a',
      Γ ⊢< Ax (ty n) > A ≡ A' : Sort (ty n) →
      Γ ,, (ty n , A) ⊢< Ax (ty m) > B ≡ B' : Sort (ty m) →
      Γ ⊢< ty n > a ⟹ a' : A →
      Γ ⊢< ty m > b : B <[a..] →
      Γ ⊢< ty n > pi1 (ty n) (ty m) A B (pair (ty n) (ty m) A' B' a b) ⟹ a' : A

| ortho_pi2pair :
    ∀ Γ n m A B A' B' a b b',
      Γ ⊢< Ax (ty n) > A ≡ A' : Sort (ty n) →
      Γ ,, (ty n , A) ⊢< Ax (ty m) > B ≡ B' : Sort (ty m) →
      Γ ⊢< ty n > a : A →
      Γ ⊢< ty m > b ⟹ b' : B <[a..] →
      Γ ⊢< ty m > pi2 (ty n) (ty m) A B (pair (ty n) (ty m) A' B' a b) ⟹ b' : B<[a..]

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


| ortho_cast_univ :
    ∀ Γ i e a a',
      Γ ⊢< prop > e : Eq (Ax (Ax i)) (Sort (Ax i)) (Sort i) (Sort i) ->
      Γ ⊢< Ax i > a ⟹ a' : Sort i ->
      Γ ⊢< Ax i > cast (Ax i) (Sort i) (Sort i) e a ⟹ a' : Sort i

| ortho_cast_nat :
    ∀ Γ e a a',
      Γ ⊢< prop > e : Eq (Ax (ty 0)) (Sort (ty 0)) Nat Nat ->
      Γ ⊢< ty 0 > a ⟹ a' : Nat ->
      Γ ⊢< ty 0 > cast (ty 0) Nat Nat e a ⟹ a' : Nat

| ortho_cast_pi :
  ∀ Γ i n A1 A1' A2 A2' B1 B1' B2 B2' e e' f f',
    Γ ⊢< Ax i > A1 ⟹ A1' : Sort i ->
    Γ ,, (i, A1) ⊢< Ax (ty n) > B1 ⟹ B1' : Sort (ty n) ->
    Γ ⊢< Ax i > A2 ⟹ A2' : Sort i ->
    Γ ,, (i, A2) ⊢< Ax (ty n) > B2 ⟹ B2' : Sort (ty n) ->
    Γ ⊢< prop > e ⟹ e' : Eq (Ax (Ru i (ty n))) (Sort (Ru i (ty n))) (Pi i (ty n) A1 B1) (Pi i (ty n) A2 B2) ->
    Γ ⊢< Ru i (ty n) > f ⟹ f' : Pi i (ty n) A1 B1 ->
    let A1_ := S ⋅ A1' in
    let A2_ := S ⋅ A2' in
    let B1_ := (up_ren S) ⋅ B1' in
    let B2_ := (up_ren S) ⋅ B2' in
    let t1 := cast i A2_ A1_ (injpi1 i (ty n) A1_ A2_ B1_ B2_ (S ⋅ e')) (var 0) in
    let t2 := app i (ty n) A1_ B1_ (S ⋅ f') t1 in
    let t3 := cast (ty n) (B1' <[t1.: S >> var]) B2' (injpi2 i (ty n) A1_ A2_ B1_ B2_ (S ⋅ e') (var 0)) t2 in
    let t4 := lam i (ty n) A2' B2' t3 in
    Γ ⊢< Ru i (ty n) > cast (Ru i (ty n)) (Pi i (ty n) A1 B1) (Pi i (ty n) A2 B2) e f ⟹ t4 : Pi i (ty n) A2 B2      

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
  intros. induction H; eauto using ortho_red, conv_refl, ortho_irrel, typing.
Qed.


Theorem ortho_to_conv :
  forall Γ l t u A,
    Γ ⊢< l > t ⟹ u : A ->
    Γ ⊢< l > t ≡ u : A.
Proof.
  intros.
  induction H; eauto using conversion, validity_conv_left.
  - eapply conv_trans.
    1:eapply conv_beta'; eauto using validity_conv_left, conv_ty_in_ctx_ty, type_conv.
    eapply subst_conv; eauto using validity_conv_left, validity_ty_ctx, substs_one.
  - eapply conv_trans.
    1:eapply conv_pi1pair'; eauto using validity_conv_left.
    eauto.
  - eapply conv_trans.
    1:eapply conv_pi2pair'; eauto using validity_conv_left.
    eauto.
  - eapply conv_trans. eapply conv_rec_succ; eauto using validity_conv_left.
    eapply subst_conv; eauto using validity_conv_ctx.
    2:rasimpl;reflexivity.
    eapply conv_scons_alt. eapply substs_one; eauto.
    eapply conv_rec; eauto using validity_conv_left.
  - eapply conv_trans. eapply conv_J_refl'; eauto using validity_conv_left.
    eapply conv_conv; eauto. eapply subst_conv; eauto using validity_ty_ctx, substs_one, conv_refl.
  - eapply conv_trans.
    1:eapply conv_lower_lift'; eauto using validity_conv_left.
    eauto.
  - eapply conv_trans.
    1:eapply conv_lift_lower'; eauto using validity_conv_left.
    eauto.
  - eapply conv_trans.
    1:econstructor; eauto using conversion, validity_conv_left.
    eapply conv_conv.
    + eapply conv_cast_pi; eauto using validity_conv_right, conv_ty_in_ctx_ty. 
      * eapply type_conv; eauto using validity_conv_right.
        econstructor; eauto using conversion, validity_conv_left, validity_ty_ctx.
      * eapply type_conv; eauto using validity_conv_right.
        econstructor; eauto using validity_conv_left.
    + eapply conv_sym. econstructor; eauto using validity_conv_left.
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

  (* solves most goals, which are easy *)
  all: try solve [ intros ; try econstructor ; eauto 8 using WellRen_up, ctx_cons, varty_ren, ortho_validity_left, conv_ren,
              validity_conv_left, type_ren, typing ].

  (* solves remaining goals involving "congruence" rules *)
  1-5 : solve [intros; cbn in *; eapply ortho_meta_conv ;
            [ (econstructor ; eauto ; try solve [ (eapply meta_conv_conv + eapply meta_conv + eapply ortho_meta_conv) ;
              [ eauto 13 using WellRen_up, WellRen_meta, ctx_typing, typing, ctx_cons, ortho_validity_left, conv_ren, validity_conv_left, type_ren, type_nat, ortho_meta_conv
              | rasimpl ; reflexivity]])
            | ssimpl; reflexivity]].

  (* solves all goals involving computation rules, except ortho_cast_pi *)          
  all:try solve [intros; cbn in *; eapply ortho_meta_conv2 ;
            [ ((eapply ortho_beta + eapply ortho_rec_zero + eapply ortho_rec_succ + eapply ortho_J_refl + 
                eapply ortho_lower_lift + eapply ortho_lift_lower + eapply ortho_pi1pair + eapply ortho_pi2pair) ;
              try solve [ (eapply meta_conv_conv + eapply meta_conv + eapply ortho_meta_conv) ;
              [ eauto 12 using WellRen_up, ctx_cons, ortho_validity_left, conv_ren, validity_conv_left, type_ren, type_nat, ortho_meta_conv
              | ssimpl ; reflexivity]])
            | ssimpl; reflexivity | ssimpl; reflexivity ]].            

  (* ortho_cast_pi *)
  - intros. eapply ortho_meta_conv2.
    + eapply ortho_cast_pi; fold ren_term; eapply ortho_meta_conv.
      1,3,5,7,9,11:eauto 12 using WellRen_up, ctx_cons, ortho_validity_left, conv_ren, validity_conv_left, type_ren, type_nat, ortho_meta_conv.
      all:rasimpl;reflexivity.
    + fold ren_term. rasimpl. reflexivity.
    + fold ren_term. unfold_all_local. simpl.
      f_equal. rasimpl. f_equal. f_equal. f_equal. rasimpl. f_equal. f_equal; substify; asimpl; reflexivity.
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
  induction H; intros.

  (* variable case *)
  1:cbn;eauto using subst_ortho_var.

  (* irrelevance case *)
  20:{ eapply ortho_irrel. 2:eapply type_conv.
    1,2:eapply subst_ty ; eauto using validity_subst_conv_left, validity_subst_conv_right, ortho_subst_to_conv, validity_ty_ctx.
    eapply conv_sym, subst_conv; eauto using ortho_subst_to_conv, validity_ty_ty, conv_refl. }

  (* solves most easy, goals *)
  all: try solve [ intros ; try econstructor ;
            eauto 11 using ortho_subst_up, ctx_cons, ortho_validity_left, subst_conv,
              validity_conv_left, ortho_subst_to_conv,  refl_subst, validity_subst_conv_left  ].

  (* needed in some of the following cases *)
  all: try (assert (Δ,, (ty 0, Nat) ⊢< Ax l > P <[ up_term_term σ] : Sort l)
  by (eapply subst_ty; eauto using type_nat, ctx_cons, ortho_validity_left;
  eapply WellSubst_up; eauto using type_nat, ortho_subst_to_conv, validity_subst_conv_left)).

  (* solves remaining goals involving "congruence" rules *)
  1-5:try solve [intros ; cbn in * ; eapply ortho_meta_conv ;
            [ (econstructor ; eauto ; try solve [ (eapply meta_conv_conv + eapply meta_conv + eapply ortho_meta_conv) ;
              [ eauto 20 using ctx_cons, ortho_validity_left, validity_conv_left, type_nat, ortho_subst_up, subst_conv, ortho_subst_to_conv
              | rasimpl ; reflexivity]])
            | ssimpl; reflexivity]].
            
  (* solves most goals involving computaiton rules *)            
  all:try solve [intros; cbn in *; eapply ortho_meta_conv2 ;
            [ ((eapply ortho_beta + eapply ortho_rec_zero + eapply ortho_rec_succ + eapply ortho_J_refl + 
                eapply ortho_lower_lift + eapply ortho_lift_lower + eapply ortho_pi1pair + eapply ortho_pi2pair +
                eapply ortho_cast_nat + eapply ortho_cast_univ) ;
              try solve [ (eapply meta_conv_conv + eapply meta_conv + eapply ortho_meta_conv) ;
              [ eauto 13 using WellRen_up, ctx_cons, ortho_validity_left, conv_ren, validity_conv_left, type_ren, type_nat, ortho_meta_conv, ortho_subst_to_conv, validity_subst_conv_left, ortho_subst_up, subst_conv, refl_subst, subst_ty, WellSubst_up
              | ssimpl ; reflexivity]])
            | ssimpl; reflexivity | ssimpl; reflexivity ]].

  (* for some strange reason, the following goals (rec_zero and rec_succ) are not solved by the automation *)
  - cbn. eapply ortho_meta_conv2. eapply ortho_rec_zero; eauto.
    1: eapply ortho_meta_conv; eauto; rasimpl; reflexivity.
    2,3:rasimpl;reflexivity.
    eapply subst_ty; eauto using ctx_cons, type_nat.
    eapply WellSubst_up. eapply WellSubst_up.
    all:rasimpl; eauto using type_nat, ortho_subst_to_conv, validity_subst_conv_left.
  - cbn. eapply ortho_meta_conv2. eapply ortho_rec_succ; eauto.
    1-3:eapply ortho_meta_conv; eauto 8 using ctx_cons, type_nat, ortho_subst_up;  rasimpl; reflexivity.
    all:rasimpl;reflexivity.      
  - eapply ortho_meta_conv2.
    + eapply ortho_cast_pi; fold subst_term; eapply ortho_meta_conv.
      1,3,5,7,9,11:eauto 13 using WellRen_up, ctx_cons, ortho_validity_left, conv_ren, validity_conv_left, type_ren, type_nat, ortho_meta_conv, ortho_subst_to_conv, validity_subst_conv_left, ortho_subst_up, subst_conv, refl_subst, subst_ty, WellSubst_up.
      all:rasimpl;reflexivity.
    + fold subst_term; rasimpl; reflexivity.
    + fold subst_term. unfold_all_local. simpl.
      f_equal. rasimpl. f_equal. f_equal. f_equal. rasimpl. f_equal.
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

Lemma ortho_sigma_inv Γ l1 l2 l' t' A B T :
  Γ ⊢< l' > Sigma l1 l2 A B ⟹ t' : T →
  exists A' B' n m,
    l1 = ty n /\
    l2 = ty m /\
    t' = Sigma (ty n) (ty m) A' B'  ∧
    l' =  Ax (ty (max n m)) ∧
    Γ ⊢< Ax (ty n) > A ⟹ A' : Sort (ty n) ∧
    Γ ,, (ty n, A) ⊢< Ax (ty m) > B ⟹ B' : Sort (ty m) ∧
    Γ ⊢< Ax (Ax (ty (max n m))) > Sort (ty (max n m)) ≡ T : Sort (Ax (ty (max n m))).
Proof.
  intros.
  dependent induction H; eauto. 
  all:assert (⊢ Γ) by eauto using ortho_to_conv, validity_conv_ctx, validity_ty_ctx.
  - eauto 12 using  conv_sort.
  - repeat destruct IHortho_red as (? & IHortho_red). subst.
    eauto 12 using conv_sym, conv_trans.
  - eapply type_inv in H. dependent destruction H.
    destruct l2; inversion lvl_eq.
Qed.

Lemma ortho_pair_inv Γ l1 l2 l' t' A B a b T :
  Γ ⊢< l' > pair l1 l2 A B a b ⟹ t' : T →
  exists A' B' a' b' n m,
    l1 = ty n /\
    l2 = ty m /\
    t' = pair (ty n) (ty m) A' B' a' b'  ∧
    l' =  ty (max n m) ∧
    Γ ⊢< Ax (ty n) > A ≡ A' : Sort (ty n) ∧
    Γ ,, (ty n, A) ⊢< Ax (ty m) > B ≡ B' : Sort (ty m) ∧
    Γ ⊢< ty n > a ⟹ a' : A /\
    Γ ⊢< ty m > b ⟹ b' : B<[a..] /\
    Γ ⊢< Ax (ty (max n m)) > Sigma (ty n) (ty m) A B ≡ T : Sort (ty (max n m)).
Proof.
  intros.
  dependent induction H; eauto. 
  all:assert (⊢ Γ) by eauto using ortho_to_conv, validity_conv_ctx, validity_ty_ctx.
  - eauto 19 using conv_refl, validity_conv_left, typing.
  - repeat destruct IHortho_red as (? & IHortho_red). subst.
    eauto 18 using conv_sym, conv_trans.
  - eapply type_inv in H. dependent destruction H.
    destruct l2; inversion lvl_eq.
Qed.

Lemma ortho_pi1_inv Γ l1 l2 l' t' A B u T :
  Γ ⊢< l' > pi1 l1 l2 A B u ⟹ t' : T →
  exists n m, 
    l1 = ty n /\
    l2 = ty m /\
    l' = ty n /\ 
    Γ ⊢< Ax (ty n) > A ≡ T : Sort (ty n) /\
    ((exists A' B' u', 
      t' = pi1 (ty n) (ty m) A' B' u' /\
      Γ ⊢< Ax (ty n) > A ≡ A' : Sort (ty n) ∧
      Γ ,, (ty n, A) ⊢< Ax (ty m) > B ≡ B' : Sort (ty m) ∧
      Γ ⊢< ty (max n m) > u ⟹ u' : Sigma (ty n) (ty m) A B
    ) \/   
    (exists A' B' a b a', 
      u = pair (ty n) (ty m) A' B' a b /\
      Γ ⊢< Ax (ty n) > A ≡ A' : Sort (ty n) ∧
      Γ ,, (ty n, A) ⊢< Ax (ty m) > B ≡ B' : Sort (ty m) ∧
      Γ ⊢< ty n > a ⟹ a' : A /\
      Γ ⊢< ty m > b : B<[ a..] /\
      t' = a')).
Proof.
  intros.
  dependent induction H.
  - eexists. eexists. intuition eauto 8 using validity_conv_left, ortho_validity_left, subst_conv, substs_one, validity_conv_ctx, conv_refl.
  - repeat destruct IHortho_red as (? & IHortho_red). subst.
    eauto 18 using conv_sym, conv_trans. 
  - eapply type_inv in H. dependent destruction H.
    destruct l2; inversion lvl_eq.
  - eexists. eexists. intuition eauto 8 using validity_conv_left, ortho_validity_left, subst_conv, substs_one, validity_conv_ctx, conv_refl.
    right. eauto 13.
Qed.

Lemma ortho_pi2_inv Γ l1 l2 l' t' A B u T :
  Γ ⊢< l' > pi2 l1 l2 A B u ⟹ t' : T →
  exists n m, 
    l1 = ty n /\
    l2 = ty m /\
    l' = ty m /\ 
    Γ ⊢< Ax (ty m) > B<[(pi1 (ty n) (ty m) A B u)..] ≡ T : Sort (ty m) /\
    ((exists A' B' u', 
      t' = pi2 (ty n) (ty m) A' B' u' /\
      Γ ⊢< Ax (ty n) > A ≡ A' : Sort (ty n) ∧
      Γ ,, (ty n, A) ⊢< Ax (ty m) > B ≡ B' : Sort (ty m) ∧
      Γ ⊢< ty (max n m) > u ⟹ u' : Sigma (ty n) (ty m) A B
    ) \/   
    (exists A' B' a b b', 
      u = pair (ty n) (ty m) A' B' a b /\
      Γ ⊢< Ax (ty n) > A ≡ A' : Sort (ty n) ∧
      Γ ,, (ty n, A) ⊢< Ax (ty m) > B ≡ B' : Sort (ty m) ∧
      Γ ⊢< ty n > a : A /\
      Γ ⊢< ty m > b ⟹ b' : B<[ a..] /\
      t' = b')).
Proof.
  intros.
  dependent induction H.
  all:assert (⊢ Γ) by eauto using ortho_to_conv, validity_conv_ctx, validity_ty_ctx.
  - eexists. eexists. intuition eauto 8 using validity_conv_left, ortho_validity_left, subst_conv, substs_one, validity_conv_ctx, conv_refl.
    eapply conv_refl, subst_ty; eauto 7 using validity_conv_left, subst_one, ortho_to_conv, typing.
  - repeat destruct IHortho_red as (? & IHortho_red). subst.
    eauto 18 using conv_sym, conv_trans. 
  - eapply type_inv in H. dependent destruction H.
    destruct l2; inversion lvl_eq.
  - eexists. eexists. intuition eauto 8 using validity_conv_left, ortho_validity_left, subst_conv, substs_one, validity_conv_ctx, conv_refl.
    1:eapply subst_conv; eauto 8 using validity_conv_left, conv_refl, substs_one, ortho_to_conv, conv_pi1pair'.
    right. eauto 13.
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


Lemma ortho_cast_inv Γ m l A B e a w T :
  Γ ⊢< ty m > cast l A B e a ⟹ w : T ->
  l = ty m /\ (Γ ⊢< Ax l > B ≡ T : Sort l) /\
  (* case ortho_cast *)
  ((exists A' B' e' a',
    Γ ⊢< Ax l > A ⟹ A' : Sort l /\
    Γ ⊢< Ax l > B ⟹ B' : Sort l /\
    Γ ⊢< prop > e ⟹ e' : Eq (Ax l) (Sort l) A B /\
    Γ ⊢< l > a ⟹ a' : A /\
    w = cast l A' B' e' a') 
  \/
  (* case ortho_cast_nat *)
  (exists a',
      l = ty 0 /\
      A = Nat /\ 
      B = Nat /\
      Γ ⊢< prop > e : Eq (Ax (ty 0)) (Sort (ty 0)) Nat Nat /\
      Γ ⊢< ty 0 > a ⟹ a' : Nat /\
      w = a')
  \/
  (* case ortho_cast_univ *)
  (exists a' i,
    l = Ax i /\
    A = Sort i /\
    B = Sort i /\
    Γ ⊢< prop > e : Eq (Ax (Ax i)) (Sort (Ax i)) (Sort i) (Sort i) /\
    Γ ⊢< Ax i > a ⟹ a' : Sort i /\
    w = a')
  \/
  (* case ortho_cast_pi *)
  (exists i n A1 A1' A2 A2' B1 B1' B2 B2' e' f f',
    l = Ru i (ty n) /\
    A = Pi i (ty n) A1 B1 /\
    B = Pi i (ty n) A2 B2 /\
    a = f /\
    Γ ⊢< Ax i > A1 ⟹ A1' : Sort i /\
    Γ ,, (i, A1) ⊢< Ax (ty n) > B1 ⟹ B1' : Sort (ty n) /\
    Γ ⊢< Ax i > A2 ⟹ A2' : Sort i /\
    Γ ,, (i, A2) ⊢< Ax (ty n) > B2 ⟹ B2' : Sort (ty n) /\
    Γ ⊢< prop > e ⟹ e' : Eq (Ax (Ru i (ty n))) (Sort (Ru i (ty n))) (Pi i (ty n) A1 B1) (Pi i (ty n) A2 B2) /\
    Γ ⊢< Ru i (ty n) > f ⟹ f' : Pi i (ty n) A1 B1 /\
    let A1_ := S ⋅ A1' in
    let A2_ := S ⋅ A2' in
    let B1_ := (up_ren S) ⋅ B1' in
    let B2_ := (up_ren S) ⋅ B2' in
    let t1 := cast i A2_ A1_ (injpi1 i (ty n) A1_ A2_ B1_ B2_ (S ⋅ e')) (var 0) in
    let t2 := app i (ty n) A1_ B1_ (S ⋅ f') t1 in
    let t3 := cast (ty n) (B1' <[t1.: S >> var]) B2' (injpi2 i (ty n) A1_ A2_ B1_ B2_ (S ⋅ e') (var 0)) t2 in
    let t4 := lam i (ty n) A2' B2' t3 in    
    w = t4)).
Proof.
  intros.
  dependent induction H; eauto.
  2:solve [ repeat destruct IHortho_red as (? & IHortho_red);
  destruct IHortho_red as [k | [k | [k | k]]]; repeat destruct k as (? & k); 
  subst;intuition eauto 30 using conv_sym, conv_trans ].
  1-3:solve [intuition eauto 10 using conv_refl, ortho_validity_left, validity_ty_ctx, conversion].
  - clear IHortho_red1 IHortho_red2 IHortho_red3 IHortho_red4 IHortho_red5 IHortho_red6. unfold_all_local. 
    intuition eauto 7 using conversion, ortho_validity_left, conv_refl.
    intuition eauto 30.
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
    | Sigma _ _ _ _ => eapply ortho_sigma_inv in h
    | pair _ _ _ _ _ _ => eapply ortho_pair_inv in h
    | pi1 _ _ _ _ _ => eapply ortho_pi1_inv in h
    | pi2 _ _ _ _ _ => eapply ortho_pi2_inv in h
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
    | cast _ _ _ _ _ => eapply ortho_cast_inv in h
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
  | Sigma i j A B => 1 + size A + size B 
  | pair i j A B a b => 1 + size A + size B + size a + size b 
  | pi1 i j A B t => 1 + size A + size B + size t
  | pi2 i j A B t => 1 + size A + size B + size t
  | cast i A B e t => 1 + size A + size B + size e + size t
  | _ => 0
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


Lemma conv_to_ortho_prop Γ t u A :
  Γ ⊢< prop > t ≡ u : A ->
  Γ ⊢< prop > t ⟹ u : A.
Proof.
  intros. eapply ortho_irrel; eauto using validity_conv_left, validity_conv_right.
Qed.

(* the main proof *)
Theorem ortho_diamond_ty :
  forall Γ l t t' t'' T,
    Γ ⊢< l > t ⟹ t' : T ->
    Γ ⊢< l > t ⟹ t'' : T ->
    exists t''', (Γ ⊢< l > t' ⟹ t''' : T) /\ (Γ ⊢< l > t'' ⟹ t''' : T).
Proof.
  intros Γ l t. generalize t Γ l. clear Γ l t.

  refine (@well_founded_ind _ (fun t u => size t < size u) _ _ _).
  eapply wf_inverse_image, lt_wf.
  intros t IH Γ l t' t'' T t_red_t' t_red_t''.

  destruct l.
  2:{ eexists. intuition eauto using ortho_validity_left, ortho_validity_right, ortho_irrel. }
  rename n into i.

  eapply (ortho_diamond_helper _ _ _ _ _ _ t_red_t' t_red_t'').
  assert (⊢ Γ) as ΓWf by (eauto using ortho_validity_left, validity_ty_ctx). 

  destruct t.

  (* eliminates cases in sprop *)
  all: try solve 
    [eapply ortho_validity_left in t_red_t'; eapply type_inv in t_red_t'; dependent destruction t_red_t'; inversion lvl_eq].

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


  (* sigma *)
  - rename t1 into A. rename t2 into B.
    ttinv t_red_t'. destruct t_red_t' as (A' & B' & n & m & eq1 & eq2 & t'_eq_sig & _ & A_red_A' & B_red_B' & _).
    ttinv t_red_t''. destruct t_red_t'' as (A'' & B''  & n' & m' & eq1' & eq2' & t''_eq_sig & _ & A_red_A'' & B_red_B'' & _).
    subst. ty_inj_tac. subst.

    destruct (IH A ltac:(simpl; lia) _ _ _ _ _ A_red_A' A_red_A'') as (A''' & A'_red_A''' & A''_red_A''').
    destruct (IH B ltac:(simpl; lia) _ _ _ _ _ B_red_B' B_red_B'') as (B''' & B'_red_B''' & B''_red_B''').
    do 4 eexists. eexists (Sigma _ _ A''' B''').
    split; apply ortho_sigma; eauto 7 using conv_ty_in_ctx_ortho, ortho_to_conv, conv_refl, validity_ty_ty, validity_conv_left.


  (* pair *)
  - rename t1 into A. rename t2 into B. rename t3 into a. rename t4 into b.
    ttinv t_red_t'. destruct t_red_t' as (A' & B' & a' & b' & n & m & eq1 & eq2 & t'_eq_pair & eq3 & A_red_A' & B_red_B' & a_red_a' & b_red_b' & _).
    ttinv t_red_t''. destruct t_red_t'' as (A'' & B'' & a'' & b'' & n_ & m_ & eq1_ & eq2_ & t''_eq_pair & eq3_ & A_red_A'' & B_red_B'' & a_red_a'' & b_red_b'' & _).
    subst. ty_inj_tac. subst. clear eq3_.

    destruct (IH a ltac:(simpl; lia) _ _ _ _ _ a_red_a' a_red_a'') as (a''' & a'_red_a''' & a''_red_a''').
    destruct (IH b ltac:(simpl; lia) _ _ _ _ _ b_red_b' b_red_b'') as (b''' & b'_red_b''' & b''_red_b''').


    do 4 eexists. eexists (pair _ _ A B a''' b''').
    split; apply ortho_pair; eauto using conv_ty_in_ctx_ortho, ortho_conv, conv_ty_in_ctx_conv, conv_sym, substs_one, ortho_to_conv, subst_conv.

  (* pi1 *)
  - rename t1 into A. rename t2 into B. rename t3 into u.
    ttinv t_red_t'. destruct t_red_t' as (n & m & eq1 & eq2 & eq3 & conv & H).
    ttinv t_red_t''. destruct t_red_t'' as (n' & m' & eq1' & eq2' & eq3' & _ & H').
    subst. ty_inj_tac. subst. clear eq3'.

    destruct H as [ (A' & B' & u' & t'_eq & A_conv_A' & B_conv_B' & u_red_u') | (A0 & B0 & a & b & a' & u_eq & A_conv_A0 & B_conv_B0 & a_red_a' & b_Wt & t'_eq)];
    destruct H' as [ (A'' & B'' & u'' & t''_eq & A_conv_A'' & B_conv_B'' & u_red_u'') | (A0_ & B0_ & a_ & b_ & a'' & u_eq_ & A_conv_A0_ & B_conv_B0_ & a_red_a'' & b__Wt & t_''_eq)].

    all:subst.
    all:try destruct (IH u ltac:(simpl; lia) _ _ _ _ _ u_red_u' u_red_u'') as (u''' & u'_red_u''' & u''_red_u''').

    + do 4 eexists. eexists (pi1 _ _ A B u''').
      split; apply ortho_pi1; eauto  7 using conv_sym, conv_ty_in_ctx_conv, conv_ty_in_ctx_ortho, conv_sym, ortho_conv, conv_sigma, validity_conv_left.

    + rename a_ into a. rename b_ into b. rename A0_ into A0. rename B0_ into B0.
      ttinv u_red_u'. destruct u_red_u' as (A'' & B'' & a' & b' & n & m & eq1 & eq2 & u'_eq & eq3 & A0_conv_A'' & B0_conv_B'' & a_red_a' & b_red_b' & _).
      ty_inj_tac. subst. clear eq3.
  
      assert (Γ ⊢< ty n > a ⟹ a' : A)  as temp by eauto using ortho_conv, conv_sym, conv_trans. clear a_red_a'. rename temp into a_red_a'.

      destruct (IH a ltac:(simpl; lia) _ _ _ _ _ a_red_a' a_red_a'') as (a''' & a'_red_a''' & a''_red_a''').

      do 4 eexists. exists a'''. split; eauto.
      eapply ortho_pi1pair; eauto 8 using conv_sym, conv_trans, conv_ty_in_ctx_conv, ortho_conv, type_conv, ortho_validity_right, subst_conv, substs_one, ortho_to_conv.

    + ttinv u_red_u''. destruct u_red_u'' as (A' & B' & a'' & b'' & n & m & eq1 & eq2 & u''_eq & eq3 & A0_conv_A' & B0_conv_B' & a_red_a'' & b_red_b'' & _).
      ty_inj_tac. subst. clear eq3.
  
      assert (Γ ⊢< ty n > a ⟹ a'' : A)  as temp by eauto using ortho_conv, conv_sym, conv_trans. clear a_red_a''. rename temp into a_red_a''.

      destruct (IH a ltac:(simpl; lia) _ _ _ _ _ a_red_a' a_red_a'') as (a''' & a'_red_a''' & a''_red_a''').

      do 4 eexists. exists a'''. split; eauto.
      eapply ortho_pi1pair; eauto 8 using conv_sym, conv_trans, conv_ty_in_ctx_conv, ortho_conv, type_conv, ortho_validity_right, subst_conv, substs_one, ortho_to_conv.
      
    + dependent destruction u_eq_.
      destruct (IH a ltac:(simpl; lia) _ _ _ _ _ a_red_a' a_red_a'') as (a''' & a'_red_a''' & a''_red_a''').
      do 4 eexists. exists a'''. split; eassumption.


  (* pi2 *)
  - rename t1 into A. rename t2 into B. rename t3 into u.
    ttinv t_red_t'. destruct t_red_t' as (n & m & eq1 & eq2 & eq3 & conv & H).
    ttinv t_red_t''. destruct t_red_t'' as (n' & m' & eq1' & eq2' & eq3' & _ & H').
    subst. ty_inj_tac. subst. clear eq3'.

    destruct H as [ (A' & B' & u' & t'_eq & A_conv_A' & B_conv_B' & u_red_u') | (A0 & B0 & a & b & b' & u_eq & A_conv_A0 & B_conv_B0 & a_Wt & b_red_b' & t'_eq)];
    destruct H' as [ (A'' & B'' & u'' & t''_eq & A_conv_A'' & B_conv_B'' & u_red_u'') | (A0_ & B0_ & a_ & b_ & b'' & u_eq_ & A_conv_A0_ & B_conv_B0_ & a__Wt & b_red_b''& t_''_eq)].

    all:subst.
    all:try destruct (IH u ltac:(simpl; lia) _ _ _ _ _ u_red_u' u_red_u'') as (u''' & u'_red_u''' & u''_red_u''').

    + do 4 eexists. eexists (pi2 _ _ A B u''').
      split; apply ortho_pi2; eauto  7 using conv_sym, conv_ty_in_ctx_conv, conv_ty_in_ctx_ortho, conv_sym, ortho_conv, conv_sigma, validity_conv_left.

    + rename a_ into a. rename b_ into b. rename A0_ into A0. rename B0_ into B0.
      ttinv u_red_u'. destruct u_red_u' as (A'' & B'' & a' & b' & n & m & eq1 & eq2 & u'_eq & eq3 & A0_conv_A'' & B0_conv_B'' & a_red_a' & b_red_b' & _).
      ty_inj_tac. subst. clear eq3.
  
      assert (Γ ⊢< ty m > b ⟹ b' : B <[ a..]) as temp by eauto 7 using ortho_conv, subst_conv, conv_sym, substs_one, conv_refl.
      clear b_red_b'. rename temp into b_red_b'.

      destruct (IH b ltac:(simpl; lia) _ _ _ _ _ b_red_b' b_red_b'') as (b''' & b'_red_b''' & b''_red_b''').

      do 4 eexists. exists b'''. split; eauto.
      eapply ortho_pi2pair; eauto 8 using conv_sym, conv_trans, conv_ty_in_ctx_conv, ortho_conv, type_conv, ortho_validity_right, subst_conv, substs_one, ortho_to_conv.

    + ttinv u_red_u''. destruct u_red_u'' as (A' & B' & a'' & b'' & n & m & eq1 & eq2 & u''_eq & eq3 & A0_conv_A' & B0_conv_B' & a_red_a'' & b_red_b'' & _).
      ty_inj_tac. subst. clear eq3.
  
      assert (Γ ⊢< ty m > b ⟹ b'' : B <[ a..]) as temp by eauto 7 using ortho_conv, subst_conv, conv_sym, substs_one, conv_refl.
      clear b_red_b''. rename temp into b_red_b''.

      destruct (IH b ltac:(simpl; lia) _ _ _ _ _ b_red_b' b_red_b'') as (b''' & b'_red_b''' & b''_red_b''').

      do 4 eexists. exists b'''. split; eauto.
      eapply ortho_pi2pair; eauto 8 using conv_sym, conv_trans, conv_ty_in_ctx_conv, ortho_conv, type_conv, ortho_validity_right, subst_conv, substs_one, ortho_to_conv.

    + dependent destruction u_eq_.
      destruct (IH b ltac:(simpl; lia) _ _ _ _ _ b_red_b' b_red_b'') as (b''' & b'_red_b''' & b''_red_b''').
      do 4 eexists. exists b'''. split; eassumption.


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

  (* case cast *)      
  - rename t1 into A. rename t2 into B. rename t3 into e. rename t4 into u.
    ttinv t_red_t'. destruct t_red_t' as (lvl_eq & B_conv_T & disj).
    ttinv t_red_t''. destruct t_red_t'' as (_ & _ & disj').
    subst.
    destruct disj as 
      [ (A' & B' & e' & u' & A_red_A' & B_red_B' & e_red_e' & u_red_u' & t'_eq) 
      |[ (u' & lvl_eq & A_eq & B_eq & eWt & u_red_u' & t'_eq)
      |[ (u' & i0 & lvl_eq & A_eq & B_eq & eWt & u_red_u' & t'_eq)
      | (i0 & n & A1 & A1' & A2 & A2' & B1 & B1' & B2 & B2' & e' & f & f' & 
        lvl_eq & A_eq & B_eq & u_eq & A1_red_A1' & B1_red_B1' & A2_red_A2' & B2_red_B2' & e_red_e' &
        f_red_f' & t'_eq)]]];
    destruct disj' as 
      [ (A'' & B'' & e'' & u'' & A_red_A'' & B_red_B'' & e_red_e'' & u_red_u'' & t''_eq) 
      |[ (u'' & lvl_eq' & A_eq' & B_eq' & eWt' & u_red_u'' & t''_eq)
      |[ (u'' & i0' & lvl_eq' & A_eq' & B_eq' & eWt' & u_red_u'' & t''_eq)
      | (i0'_ & n_ & A1_ & A1'' & A2_ & A2'' & B1_ & B1'' & B2_ & B2'' & e'' & f_ & f'' & 
        lvl_eq' & A_eq' & B_eq' & u_eq_ & A1_red_A1'' & B1_red_B1'' & A2_red_A2'' & B2_red_B2'' & e_red_e'' &
        f_red_f'' & t''_eq)]]].
(*         
    1-3:destruct disj' as 
      [ (A'' & B'' & e'' & u'' & A_red_A'' & B_red_B'' & e_red_e'' & u_red_u'' & t''_eq) 
      |[ (u'' & lvl_eq' & A_eq' & B_eq' & eWt' & u_red_u'' & t''_eq)
      |[ (u'' & i0' & lvl_eq' & A_eq' & B_eq' & eWt' & u_red_u'' & t''_eq)
      | (i0' & n & A1 & A1'' & A2 & A2'' & B1 & B1'' & B2 & B2'' & e'' & f & f'' & 
        lvl_eq' & A_eq' & B_eq' & u_eq & A1_red_A1'' & B1_red_B1'' & A2_red_A2'' & B2_red_B2'' & e_red_e'' &
        f_red_f'' & t''_eq)]]].


    13: destruct disj' as 
      [ (A'' & B'' & e'' & u'' & A_red_A'' & B_red_B'' & e_red_e'' & u_red_u'' & t''_eq) 
      |[ (u'' & lvl_eq' & A_eq' & B_eq' & eWt' & u_red_u'' & t''_eq)
      |[ (u'' & i0' & lvl_eq' & A_eq' & B_eq' & eWt' & u_red_u'' & t''_eq)
      | (i0'_ & n_ & A1_ & A1'' & A2_ & A2'' & B1_ & B1'' & B2_ & B2'' & e'' & f_ & f'' & 
        lvl_eq' & A_eq' & B_eq' & u_eq_ & A1_red_A1'' & B1_red_B1'' & A2_red_A2'' & B2_red_B2'' & e_red_e'' &
        f_red_f'' & t''_eq)]]].
     *)
    all:try solve [rewrite A_eq' in A_eq ; dependent destruction A_eq].



    (* ortho_cast x ortho_cast *)
    + subst. 
      destruct (IH A ltac:(simpl; lia) _ _ _ _ _ A_red_A' A_red_A'') as (A''' & A'_red_A''' & A''_red_A''').
      destruct (IH B ltac:(simpl; lia) _ _ _ _ _ B_red_B' B_red_B'') as (B''' & B'_red_B''' & B''_red_B''').
      destruct (IH e ltac:(simpl; lia) _ _ _ _ _ e_red_e' e_red_e'') as (e''' & e'_red_e''' & e''_red_e''').
      destruct (IH u ltac:(simpl; lia) _ _ _ _ _ u_red_u' u_red_u'') as (u''' & u'_red_u''' & u''_red_u''').

      do 5 eexists. split; econstructor; eauto 6 using ortho_conv, ortho_to_conv, conversion.

    (* ortho_cast x ortho_cast_nat *)
    + subst. dependent destruction lvl_eq'.
      destruct (IH u ltac:(simpl; lia) _ _ _ _ _ u_red_u' u_red_u'') as (u''' & u'_red_u''' & u''_red_u''').
      ttinv A_red_A'. ttinv B_red_B'. subst.
      do 5 eexists. split; eauto.
      eapply ortho_cast_nat; eauto using ortho_validity_right.

    (* ortho_cast x ortho_cast_univ *)
    + subst. rewrite lvl_eq' in *. clear lvl_eq'. clear i.
      ttinv A_red_A'. destruct A_red_A' as (k & _). subst.
      ttinv B_red_B'. destruct B_red_B' as (k & _). subst.
      destruct (IH u ltac:(simpl; lia) _ _ _ _ _ u_red_u' u_red_u'') as (u''' & u'_red_u''' & u''_red_u''').
      do 5 eexists. split; eauto.
      eapply ortho_cast_univ; eauto using ortho_validity_right.

    (* ortho_cast x ortho_cast_pi *)
    + subst. rename A1_ into A1. rename A2_ into A2. rename i0'_ into i0. rename n_ into n. 
      rename B1_ into B1. rename B2_ into B2. rename f_ into f. rename u' into f'. rename u_red_u' into f_red_f'.
      rewrite lvl_eq' in *. clear lvl_eq'. clear i. clear B_conv_T.
      ttinv A_red_A'. destruct A_red_A' as (A1' & B1' & A'_eq & _ & A1_red_A1' & B1_red_B1' & _). subst.
      ttinv B_red_B'. destruct B_red_B' as (A2' & B2' & A'_eq & _ & A2_red_A2' & B2_red_B2' & _). subst.

      destruct (IH f ltac:(simpl; lia) _ _ _ _ _ f_red_f' f_red_f'') as (f''' & f'_red_f''' & f''_red_f''').
      destruct (IH e ltac:(simpl; lia) _ _ _ _ _ e_red_e' e_red_e'') as (e''' & e'_red_e''' & e''_red_e''').
      destruct (IH A1 ltac:(simpl; lia) _ _ _ _ _ A1_red_A1' A1_red_A1'') as (A1''' & A1'_red_A1''' & A1''_red_A1''').
      destruct (IH A2 ltac:(simpl; lia) _ _ _ _ _ A2_red_A2' A2_red_A2'') as (A2''' & A2'_red_A2''' & A2''_red_A2''').
      destruct (IH B1 ltac:(simpl; lia) _ _ _ _ _ B1_red_B1' B1_red_B1'') as (B1''' & B1'_red_B1''' & B1''_red_B1''').
      destruct (IH B2 ltac:(simpl; lia) _ _ _ _ _ B2_red_B2' B2_red_B2'') as (B2''' & B2'_red_B2''' & B2''_red_B2''').

      cbn in t''_eq. subst. do 5 eexists. split.
      * eapply ortho_cast_pi; eauto 12 using conv_ty_in_ctx_ortho, ortho_to_conv, ortho_conv, conv_pi, conv_Eq, conv_sort, ortho_validity_left.
      * econstructor; eauto using ortho_to_conv, conv_ty_in_ctx_conv.
        (* eassert
          (Γ ,, (i0, A2'') 
            ⊢< _ > cast i0 (S ⋅ A2'') (S ⋅ A1'') (injpi1 i0 (ty n) (S ⋅ A1'') (S ⋅ A2'') (up_ren S ⋅ B1'') (up_ren S ⋅ B2'') (S ⋅ e'')) (var 0)
            ⟹ cast i0 (S ⋅ A2''') (S ⋅ A1''') (injpi1 i0 (ty n) (S ⋅ A1''') (S ⋅ A2''') (up_ren S ⋅ B1''') (up_ren S ⋅ B2''') (S ⋅ e''')) (var 0)
            : _) as cast_red_cast.
        { econstructor.
          4:eapply ortho_var; eauto using varty, ctx_typing, ortho_validity_right.
          1,2:eapply ortho_meta_conv; [eapply ortho_ren | idtac]; eauto using WellRen_S, ctx_typing, ortho_validity_right.
          eapply ortho_irrel.
          + econstructor. all:eapply type_ren; eauto 8 using ortho_validity_left, ortho_validity_right, ctx_typing, WellRen_S, WellRen_up, type_ren. 
          all:admit 
        )  *)
        econstructor; eauto using conv_ty_in_ctx_ortho, ortho_to_conv.
        ** eapply ortho_meta_conv. 
          *** eapply subst_ortho; eauto. all:admit.
          *** rasimpl. reflexivity.
        ** eapply conv_ty_in_ctx_ortho in B1''_red_B1''', B2''_red_B2'''.
           2,3:clear A1_red_A1' A2_red_A2'; eauto using ortho_to_conv.
           eapply conv_to_ortho_prop. eapply meta_conv_conv. 1:eapply conv_injpi2'.
           5:eapply conv_conv.
           1-5:eapply conv_ren; eauto 8 using ortho_to_conv, WellRen_S, WellRen_up, ctx_typing, ortho_validity_left, type_ren.
           1:rasimpl; econstructor; eauto using conversion, ortho_validity_left, validity_ty_ctx.
           1,2:econstructor.
           1,4:eapply type_ren.
          all:admit.

        
        ** eapply ortho_meta_conv.
          *** econstructor.
            1:eauto 7 using ortho_to_conv, ortho_meta_conv, ortho_ren, ctx_typing, ortho_validity_left, WellRen_S.
            2:{ eapply ortho_conv. eapply ortho_ren; eauto using ctx_typing, ortho_validity_left, WellRen_S. 
                econstructor; fold ren_term. all:admit. }
            all:admit.
          *** rasimpl. reflexivity.


    (* ortho_cast_nat x ortho_cast *)
    + admit.

    (* ortho_cast_nat x ortho_cast_nat *)
    + admit.

    (* ortho_cast_univ x ortho_cast *)
    + admit.

    (* ortho_cast_univ x ortho_cast_univ *)
    + admit.

    (* ortho_cast_pi x ortho_cast *)
    + admit.

    (* ortho_cast_pi x ortho_cast_pi *)
    + subst A B u. inversion A_eq. subst. inversion B_eq. subst. clear A_eq B_eq.
      rewrite lvl_eq in *. clear lvl_eq lvl_eq' i.
      admit.
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

Ltac equiv_red_ind_aux0 := 
  ty_inj_tac ; subst ;
  try solve [ econstructor ; eauto 9 using equiv_to_conv, validity_conv_left,
      validity_conv_right, conv_Eq, conv_Lift, type_conv, conv_refl, subst_conv, substs_one, validity_ty_ctx, conv_sym ];
  try solve [ eapply type_conv ; 
    [ econstructor ; eauto 9 using equiv_to_conv, validity_conv_left, conv_ty_in_ctx_ty,
        validity_conv_right, conv_Eq, conv_Lift, type_conv, conv_refl, subst_conv, substs_one, validity_ty_ctx, conv_sym 
    | eauto 11 using equiv_to_conv, validity_conv_left, subst_conv, substs_one, conv_sym, validity_ty_ctx, conv_refl]].

Ltac equiv_red_ind_aux1 := 
  intros _t _u _t_conv_u _deriv ; 
  eapply type_inv in _deriv ; 
  dependent destruction _deriv ;
  equiv_red_ind_aux0.

Ltac equiv_red_ind_aux2 := 
  intros _t _u _t_red_u _deriv ; 
  eapply type_inv in _deriv ; 
  dependent destruction _deriv ;
  ty_inj_tac ; subst ;
  eapply equiv_step ;
  try solve [ econstructor ; eauto 9 using equiv_to_conv, validity_conv_left, ortho_refl, ortho_conv, ortho_to_conv,
      validity_conv_right, conv_Eq, conv_Lift, type_conv, conv_refl, subst_conv, substs_one, validity_ty_ctx, conv_sym ];
  try solve [ eapply ortho_conv ; 
    [ econstructor ; eauto 9 using equiv_to_conv, validity_conv_left, conv_ty_in_ctx_ty, ortho_refl, ortho_conv, conv_ty_in_ctx_ortho,
        validity_conv_right, conv_Eq, conv_Lift, type_conv, conv_refl, subst_conv, substs_one, validity_ty_ctx, conv_sym 
    | eauto 11 using equiv_to_conv, validity_conv_left, subst_conv, substs_one, conv_sym, validity_ty_ctx, conv_refl, ortho_to_conv]].

Ltac equiv_red_ind_aux := 
  try solve [ equiv_red_ind_aux1 ];
  try solve [ equiv_red_ind_aux2 ];
  try solve [ equiv_red_ind_aux0 ].



Lemma equiv_pi Γ i j A B A' B' :
      Γ ⊢< Ax i > A ≈ A' : Sort i →
      Γ ,, (i , A) ⊢< Ax j > B ≈ B' : Sort j →
      Γ ⊢< Ax (Ru i j) > Pi i j A B ≈ Pi i j A' B' : Sort (Ru i j).
Proof.
  intros A_equiv_A' B_equiv_B'.
  eapply equiv_trans.
  - refine (equiv_red_ind (fun _ => Sort (Ru i j)) (fun B => Pi i j A B) _ _ B_equiv_B' _); equiv_red_ind_aux.
  - refine (equiv_red_ind (fun _ => Sort (Ru i j)) (fun A => Pi i j A B') _ _ A_equiv_A' _); equiv_red_ind_aux.
Qed.

Lemma equiv_sigma Γ n m A B A' B' :
      Γ ⊢< Ax (ty n) > A ≈ A' : Sort (ty n) →
      Γ ,, (ty n, A) ⊢< Ax (ty m) > B ≈ B' : Sort (ty m) →
      Γ ⊢< Ax (ty (max n m)) > Sigma (ty n) (ty m) A B ≈ Sigma (ty n) (ty m) A' B' : Sort (ty (max n m)).
Proof.
  intros A_equiv_A' B_equiv_B'.
  eapply equiv_trans.
  - refine (equiv_red_ind (fun _ => _) (fun B => Sigma _ _ A B) _ _ B_equiv_B' _); equiv_red_ind_aux.
  - refine (equiv_red_ind (fun _ => Sort (ty (max n m))) (fun A => Sigma (ty n) (ty m) A B') _ _ A_equiv_A' _); equiv_red_ind_aux.
Qed.


Lemma equiv_pair Γ n m A B a b A' B' a' b' :
      Γ ⊢< Ax (ty n) > A ≡ A' : Sort (ty n) →
      Γ ,, (ty n , A) ⊢< Ax (ty m) > B ≡ B' : Sort (ty m) →
      Γ ⊢< ty n > a ≈ a' : A →
      Γ ⊢< ty m > b ≈ b' : B <[a..] →
      Γ ⊢< ty (max n m) > pair (ty n) (ty m) A B a b ≈ pair (ty n) (ty m) A' B' a' b' : Sigma (ty n) (ty m) A B.
Proof.
  intros A_conv_A' B_conv_B' a_equiv_a' b_equiv_b'.
  eapply equiv_trans. eapply equiv_trans.
  - refine (equiv_red_ind (fun _ => _) (fun a => pair _ _ _ _ a _) _ _ a_equiv_a' _); equiv_red_ind_aux.
  - refine (equiv_red_ind (fun _ => _) (fun b => pair _ _ _ _ _ b) _ _ b_equiv_b' _).
    + equiv_red_ind_aux1.
    + equiv_red_ind_aux2.
    + eapply type_conv.
      * econstructor; 
        eauto 13 using equiv_to_conv, validity_conv_right, ortho_refl, type_conv, subst_conv, validity_conv_left, conv_refl, substs_one, validity_ty_ctx.
      * econstructor; eauto using equiv_to_conv, validity_conv_left, conv_refl.
  - eapply equiv_step; econstructor; 
    eauto 13 using equiv_to_conv, validity_conv_right, ortho_refl, type_conv, subst_conv, validity_conv_left, conv_refl, substs_one, validity_ty_ctx.
Qed.

Lemma equiv_pi1 Γ n m A B t A' B' t' :
      Γ ⊢< Ax (ty n) > A ≡ A' : Sort (ty n) →
      Γ ,, (ty n , A) ⊢< Ax (ty m) > B ≡ B' : Sort (ty m) →
      Γ ⊢< ty (max n m) > t ≈ t' : Sigma (ty n) (ty m) A B →
      Γ ⊢< ty n > pi1 (ty n) (ty m) A B t ≈ pi1 (ty n) (ty m) A' B' t' : A.
Proof.
  intros A_conv_A' B_conv_B' t_equiv_t'.
  eapply equiv_trans.
  - refine (equiv_red_ind (fun _ => _) (fun t => pi1 _ _ _ _ t) _ _ t_equiv_t' _); equiv_red_ind_aux.
  - eapply equiv_step. econstructor; eauto using equiv_to_conv, validity_conv_right, ortho_refl.
Qed.
  
Lemma equiv_pi2 Γ n m A B t A' B' t' :
      Γ ⊢< Ax (ty n) > A ≡ A' : Sort (ty n) →
      Γ ,, (ty n , A) ⊢< Ax (ty m) > B ≡ B' : Sort (ty m) →
      Γ ⊢< ty (max n m) > t ≈ t' : Sigma (ty n) (ty m) A B →
      Γ ⊢< ty m > pi2 (ty n) (ty m) A B t ≈ pi2 (ty n) (ty m) A' B' t' : B <[(pi1 (ty n) (ty m) A B t)..].
Proof.
  intros A_conv_A' B_conv_B' t_equiv_t'.
  eapply equiv_trans.
  - refine (equiv_red_ind (fun t => B <[(pi1 (ty n) (ty m) A B t)..]) (fun t => pi2 _ _ _ _ t) _ _ t_equiv_t' _); equiv_red_ind_aux.
  - eapply equiv_step. eapply ortho_conv. 1:econstructor; eauto using equiv_to_conv, validity_conv_right, ortho_refl.
    eapply subst_conv; eauto 10 using validity_conv_left, validity_ty_ctx, conv_refl, substs_one, conv_pi1, equiv_to_conv, conv_sym.
Qed.

Lemma equiv_lam Γ i j A B t A' B' t' :
      Γ ⊢< Ax i > A ≡ A' : Sort i →
      Γ ,, (i , A) ⊢< Ax j > B ≡ B': Sort j →
      Γ ,, (i , A) ⊢< j > t ≈ t' : B →
      Γ ⊢< Ru i j > lam i j A B t ≈ lam i j A' B' t' : Pi i j A B.
Proof.
  intros.
  eapply equiv_trans.
  - refine (equiv_red_ind (fun _ => Pi i j A B) (fun t => lam i j A B t) _ _ H1 _); equiv_red_ind_aux.
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
  - refine (equiv_red_ind (fun _ => B <[ u ..]) (fun t => app i j A B t u) _ _ H1 _); equiv_red_ind_aux.
  - refine (equiv_red_ind (fun u => B <[ u ..]) (fun u => app i j A B t' u) _ _ H2 _); equiv_red_ind_aux.
  - apply equiv_step. eapply ortho_conv.
    + eauto 8 using ortho_app, validity_conv_right, equiv_to_conv, ortho_refl.
    + eapply subst_conv; eauto using substs_one, equiv_to_conv, validity_conv_ctx, validity_conv_left, conv_refl, conv_sym.
Qed.

Lemma equiv_succ Γ t t' :
      Γ ⊢< ty 0 > t ≈ t' : Nat ->
      Γ ⊢< ty 0 > succ t ≈ succ t' : Nat.
Proof.
  intro t_equiv_t'.
  refine (equiv_red_ind (fun _ => Nat) (fun t => succ t) _ _ t_equiv_t' _); equiv_red_ind_aux.
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
  - refine (equiv_red_ind (fun _ => P <[ t.. ]) (fun p_zero => rec l P p_zero p_succ t) _ _ p_zero_equiv_p_zero' _); equiv_red_ind_aux.
  - refine (equiv_red_ind (fun _ => P <[ t.. ]) (fun p_succ => rec l P p_zero' p_succ t) _ _ p_succ_equiv_p_succ' _); equiv_red_ind_aux.
  - refine (equiv_red_ind (fun t => P <[ t.. ]) (fun t => rec l P p_zero' p_succ' t) _ _ t_equiv_t' _); equiv_red_ind_aux.
  - eapply (equiv_conv _ _ (P <[ t'..])).
    2: eapply subst_conv; eauto using substs_one, equiv_to_conv, validity_conv_ctx, validity_conv_left, conv_refl, conv_sym.
    refine (equiv_red_ind (fun P => P <[ t'.. ]) (fun P => rec l P p_zero' p_succ' t') _ _ P_equiv_P' _).
    + (* adding all the required lemmas to the eauto database of equiv_red_ind_aux1 would make 
        other cases too slow, so we handle this case manually *)
      intros; apply type_inv in H0; dependent destruction H0.
      apply type_rec; eauto 9 using equiv_to_conv, subst_conv, type_conv, type_zero,
        subst_one, validity_ty_ctx, validity_conv_left, conv_sym, conv_ty_in_ctx_ty, subst_id_var1, ctx_from_conv, refl_subst.
    + equiv_red_ind_aux2.
    + equiv_red_ind_aux0.
Qed.

Lemma equiv_Eq Γ l A A' a a' b b' :
  Γ ⊢< Ax l > A ≈ A' : Sort l ->
  Γ ⊢< l > a ≈ a' : A ->
  Γ ⊢< l > b ≈ b' : A ->
  Γ ⊢< Ax prop > Eq l A a b ≈ Eq l A' a' b' : Sort prop.
Proof.
  intros A_equiv_A' a_equiv_a' b_equiv_b'.
  eapply equiv_trans. eapply equiv_trans.
  - refine (equiv_red_ind (fun _ => Sort prop) (fun b => Eq l A a b) _ _ b_equiv_b' _); equiv_red_ind_aux.
  - refine (equiv_red_ind (fun _ => Sort prop) (fun a => Eq l A a b') _ _ a_equiv_a' _); equiv_red_ind_aux.
  - refine (equiv_red_ind (fun _ => Sort prop) (fun A => Eq l A _ _) _ _ A_equiv_A' _); equiv_red_ind_aux.
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
  - refine (equiv_red_ind _ (fun a => J l i A a P p b e) _ _ a_equiv_a' _); equiv_red_ind_aux.
  - refine (equiv_red_ind _ (fun e => J l i A _ P p b e) _ _ e_equiv_e' _).
  (* 3:equiv_red_ind_aux0. *)
    3:eapply type_J; eauto 13 using equiv_to_conv, validity_conv_left, validity_conv_right,
        type_conv, conv_Eq, conv_refl, substs_one, validity_ty_ctx, subst_conv.
    + equiv_red_ind_aux1.
    + equiv_red_ind_aux2.
  - refine (equiv_red_ind _ (fun p => J l i A _ P p b _) _ _ p_equiv_p' _).
    3:eapply type_J; eauto 13 using equiv_to_conv, validity_conv_left, validity_conv_right,
        type_conv, conv_Eq, conv_refl, substs_one, validity_ty_ctx, subst_conv.
    + equiv_red_ind_aux1.
    + equiv_red_ind_aux2.
  - refine (equiv_red_ind (fun b => P<[b..]) (fun b => J l i A _ P _ b _) _ _ b_equiv_b' _).
    3:eapply type_J; eauto 13 using equiv_to_conv, validity_conv_left, validity_conv_right,
        type_conv, conv_Eq, conv_refl, substs_one, validity_ty_ctx, subst_conv.
    + equiv_red_ind_aux1.
    + equiv_red_ind_aux2.
  - refine (equiv_red_ind _ (fun A => J l i A _ P _ _ _) _ _ A_equiv_A' _).
    3:eapply type_conv.
    3:eapply type_J; eauto 13 using equiv_to_conv, validity_conv_left, validity_conv_right,
        type_conv, conv_Eq, conv_refl, substs_one, validity_ty_ctx, subst_conv.
    3:eauto 11 using equiv_to_conv, validity_conv_left, subst_conv, substs_one, conv_sym, validity_ty_ctx, conv_refl.
    + equiv_red_ind_aux1.
    + equiv_red_ind_aux2.
  - refine (equiv_red_ind (fun P => P<[b..]) (fun P => J l i _ _ P _ _ _) _ _ P_equiv_P' _).
    3:eapply type_conv.
    3:eapply type_J; eauto 13 using equiv_to_conv, validity_conv_left, validity_conv_right,
        type_conv, conv_Eq, conv_refl, substs_one, validity_ty_ctx, subst_conv, conv_ty_in_ctx_ty.
    3:eauto 11 using equiv_to_conv, validity_conv_left, subst_conv, substs_one, conv_sym, validity_ty_ctx, conv_refl.
    + equiv_red_ind_aux1.
    + equiv_red_ind_aux2.
Qed.

Lemma equiv_Lift Γ l A A' : 
  Γ ⊢< Ax l > A ≈ A' : Sort l ->
  Γ ⊢< Ax (Ax l) > Lift l A ≈ Lift l A' : Sort (Ax l).
Proof.
  intros A_equiv_A'. refine (equiv_red_ind _ (fun A => Lift l A) _ _ A_equiv_A' _); equiv_red_ind_aux.
Qed.

Lemma equiv_lift Γ l A A' a a' : 
  Γ ⊢< Ax l > A ≈ A' : Sort l ->
  Γ ⊢< l > a ≈ a' : A ->
  Γ ⊢< Ax l > lift l A a ≈ lift l A' a' : Lift l A.
Proof.
  intros A_equiv_A' a_equiv_a'. eapply equiv_trans.
  - refine (equiv_red_ind _ (fun a => lift l A a) _ _ a_equiv_a' _); equiv_red_ind_aux.
  - refine (equiv_red_ind (fun A => Lift _ A) (fun A => lift l A _) _ _ A_equiv_A' _); equiv_red_ind_aux.
Qed.
  

Lemma equiv_lower Γ l A A' a a' : 
  Γ ⊢< Ax l > A ≈ A' : Sort l ->
  Γ ⊢< Ax l > a ≈ a' : Lift l A ->
  Γ ⊢< l > lower l A a ≈ lower l A' a' : A.
Proof.
  intros A_equiv_A' a_equiv_a'. eapply equiv_trans.
  - refine (equiv_red_ind _ (fun a => lower l A a) _ _ a_equiv_a' _); equiv_red_ind_aux.
  - refine (equiv_red_ind (fun A => A) (fun A => lower l A _) _ _ A_equiv_A' _); equiv_red_ind_aux.
Qed.

Lemma conv_to_equiv Γ l t u A :
  Γ ⊢< l > t ≡ u : A -> Γ ⊢< l > t ≈ u : A.
Proof.
  intro H. induction H.
  all : try solve [apply equiv_step; econstructor; eauto using conv_refl, ortho_refl ].
  all : eauto using equiv_pi, equiv_lam, equiv_app, equiv_succ,
    equiv_rec, equiv_conv, equiv_sym, equiv_trans, equiv_Eq, equiv_J, equiv_Lift, equiv_lower, equiv_lift,
    equiv_sigma, equiv_pair, equiv_pi1, equiv_pi2.
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


Lemma redd_conv_ty_in_ctx Γ B B' i l t u A :
  Γ ,, (i, B) ⊢< l > t ⟹* u : A -> 
  Γ ⊢< Ax i > B ≡ B' : Sort i ->
  Γ ,, (i, B') ⊢< l > t ⟹* u : A.
Proof.
  intros.
  eapply redd_conv_in_ctx; eauto.
  econstructor; eauto using validity_conv_ctx, ctx_conv_refl.
Qed.



Lemma redd_conv Γ l t u A B :
  Γ ⊢< l > t ⟹* u : A ->
  Γ ⊢< Ax l > A ≡ B : Sort l ->
  Γ ⊢< l > t ⟹* u : B.
Proof.
  intros. induction H; eauto using ortho_conv, redd_step, redd_trans.
Qed.


Definition is_type_former T :=
  match T with 
  | Sort i => True
  | Pi i j A B => True 
  | Sigma i j A B => True 
  | Nat => True 
  | Lift i A => True 
  | Eq i A a b => True 
  | _ => False 
  end.

Proposition type_former_redd Γ l U T T' : 
  is_type_former T ->
  Γ ⊢< l > T ⟹* T' : U ->
  match T with 
  | Pi l1 l2 A B => 
    exists A' B',
    T' = Pi l1 l2 A' B' /\
    Γ ⊢< Ax l1 > A ⟹* A' : Sort l1 /\
    Γ ,, (l1, A) ⊢< Ax l2 > B ⟹* B' : Sort l2
  | Sigma l1 l2 A B => 
    exists A' B',
    T' = Sigma l1 l2 A' B' /\
    Γ ⊢< Ax l1 > A ⟹* A' : Sort l1 /\
    Γ ,, (l1, A) ⊢< Ax l2 > B ⟹* B' : Sort l2
  | Sort i =>
    T' = Sort i 
  | Nat => 
    T' = Nat 
  | Eq l A a b => 
    exists A' a' b', 
    T' = Eq l A' a' b' /\ 
    Γ ⊢< Ax l > A ⟹* A' : Sort l /\ 
    Γ ⊢< l > a ⟹* a' : A /\ 
    Γ ⊢< l > b ⟹* b' : A
  | Lift l A =>
    exists A', 
    T' = Lift l A' /\
    Γ ⊢< Ax l > A ⟹* A' : Sort l
  | _ => False
  end.
Proof.
  intros is_tf T_redd_T'.
  destruct T; inversion_clear is_tf; dependent induction T_redd_T'; subst; eauto.

  all : try solve [ ttinv H ; repeat destruct H as (? & H) ; subst; repeat eexists ; intuition eauto using redd_step ].

  all : repeat destruct IHT_redd_T'1 as (? & IHT_redd_T'1); subst; 
        try edestruct IHT_redd_T'2 as (? & h); eauto; repeat destruct h as (? & h); subst ; eauto; clear IHT_redd_T'2.

  all: repeat eexists; eauto using redd_trans, redd_conv_ty_in_ctx, redd_to_conv, conv_sym, conv_trans, redd_conv.
Qed.

Proposition type_formers_inj Γ l T T1 T2 :
  Γ ⊢< l > T1 ≡ T2 : T ->
  is_type_former T1 -> 
  is_type_former T2 ->
  match T1, T2 with 
  | Pi l0 l1 A B, Pi l2 l3 A' B' =>
    l0 = l2 /\ l1 = l3 /\ Γ ⊢< Ax l0 > A ≡ A' : Sort l0 /\ Γ ,, (l0, A) ⊢< Ax l1 > B ≡ B' : Sort l1
  | Sigma l0 l1 A B, Sigma l2 l3 A' B' =>
    l0 = l2 /\ l1 = l3 /\ Γ ⊢< Ax l0 > A ≡ A' : Sort l0 /\ Γ ,, (l0, A) ⊢< Ax l1 > B ≡ B' : Sort l1
  | Lift i A, Lift i' A' =>
    i = i' /\ Γ ⊢< Ax i > A ≡ A' : Sort i
  | Nat, Nat => True 
  | Sort l, Sort l0 => l = l0 
  | Eq l A a b, Eq l' A' a' b' => 
    l = l' /\ Γ ⊢< Ax l > A ≡ A' : Sort l /\ Γ ⊢< l > a ≡ a' : A /\ Γ ⊢< l > b ≡ b' : A
  | _, _ => False 
  end.
Proof.
  intros.
  destruct T1; destruct T2; inversion_clear H0; inversion_clear H1.

  all:apply CR in H; destruct H as (t & H1 & H2).
  all:try eapply type_former_redd in H1; repeat destruct H1 as (? & H1); unfold is_type_former; eauto.
  all:try eapply type_former_redd in H2; repeat destruct H2 as (? & H2); unfold is_type_former; eauto; subst.
  all: match goal with | H : _ = _ |- _ => dependent destruction H end; subst; eauto.

  - intuition trivial.
    eauto using conv_sym, conv_trans, redd_to_conv.
    eauto 10 using conv_sym, conv_trans, redd_to_conv, conv_ty_in_ctx_conv.
   
  - intuition trivial.
    eauto using conv_sym, conv_trans, redd_to_conv.
    eauto 10 using conv_sym, conv_trans, redd_to_conv, conv_ty_in_ctx_conv.

  - intuition trivial.
    eauto using conv_sym, conv_trans, redd_to_conv.
    all:eauto 10 using conv_sym, conv_trans, redd_to_conv, conv_conv.

  - intuition trivial.
    eauto using conv_sym, conv_trans, redd_to_conv.
Qed.
