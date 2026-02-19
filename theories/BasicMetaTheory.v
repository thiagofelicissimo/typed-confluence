From Stdlib Require Import 
  Utf8 List Arith Bool Lia Setoid Morphisms Relation_Definitions.
From TypedConfluence Require Import 
  core unscoped Util Ast SubstNotations RAsimpl 
  AST_rasimpl BasicAST Flags Typing.
Require Import Equations.Prop.DepElim.
From Equations Require Import Equations.

Import ListNotations.
Import CombineNotations.

Open Scope subst_scope.

Set Default Goal Selector "!".

Derive Signature for varty.
Derive Signature for ctx_typing.
Derive Signature for typing.
Derive NoConfusion for term.
Derive NoConfusion for level.



Lemma Ax_inj l l' : Ax l = Ax l' -> l = l'.
Proof.
  intro H. destruct l; destruct l'; inversion H; auto.
Qed.


Lemma ty_inj  n n' : ty n = ty n' -> n = n'.
Proof.
  intro H. inversion H. eauto.
Qed.

Lemma conv_refl Γ t l A :
  Γ ⊢< l > t : A →
  Γ ⊢< l > t ≡ t : A.
Proof.
  induction 1.
  all: solve [ econstructor ; eauto ].
Qed.

Theorem refl_subst Γ σ Δ :
  Γ ⊢s σ : Δ →
  Γ ⊢s σ ≡ σ : Δ.
Proof.
  induction 1.
  - constructor.
  - constructor.
    + eauto.
    + apply conv_refl. assumption.
Qed.

Lemma varty_meta Γ l x A B :
  Γ ∋< l > x : A →
  A = B →
  Γ ∋< l > x : B.
Proof.
  intros h ->. exact h.
Qed.

Lemma WellRen_meta Γ Γ' Δ Δ' ρ :
  Γ ⊢r ρ : Δ →
  Γ = Γ' →
  Δ = Δ' →
  Γ' ⊢r ρ : Δ'.
Proof.
  intros ? -> ->. auto.
Qed.

#[export] Instance WellRen_morphism :
  Proper (eq ==> (`=1`) ==> eq ==> iff) WellRen.
Proof.
  intros Γ ? <- ρ ρ' e Δ ? <-.
  revert ρ ρ' e. wlog_iff. intros ρ ρ' e h.
  induction h as [| ρ Δ l A h ih ho] in ρ', e |- *.
  - constructor.
  - constructor.
    + eapply ih. intros x. unfold ">>". apply e.
    + rewrite <- e. assumption.
Qed.

Lemma autosubst_simpl_WellRen :
  ∀ Γ Δ r s,
    RenSimplification r s →
    Γ ⊢r r : Δ ↔ Γ ⊢r s : Δ.
Proof.
  intros Γ Δ r s H.
  apply WellRen_morphism. 1,3: auto.
  apply H.
Qed.

#[export] Hint Rewrite -> autosubst_simpl_WellRen : rasimpl_outermost.

Lemma WellRen_weak Γ Δ ρ l A :
  Γ ⊢r ρ : Δ →
  Γ ,, (l, A) ⊢r (ρ >> S) : Δ.
Proof.
  induction 1 as [| ρ Δ i B h ih ho] in l, A |- *.
  - constructor.
  - constructor.
    + auto.
    + eapply varty_meta.
      * unfold ">>". constructor. eassumption.
      * rasimpl. reflexivity.
Qed.

Lemma WellRen_up Γ Δ l A A' ρ :
  Γ ⊢r ρ : Δ →
  A' = ρ ⋅ A ->
  Γ ,, (l, A') ⊢r up_ren ρ : Δ ,, (l, A).
Proof.
  intros h p. subst.
  constructor.
  - rasimpl. apply WellRen_weak. assumption.
  - rasimpl. cbn. eapply varty_meta.
    + constructor.
    + rasimpl. reflexivity.
Qed.

Lemma varty_ren Γ Δ ρ x l A :
  Γ ∋< l > x : A →
  Δ ⊢r ρ : Γ →
  Δ ∋< l > ρ x : ρ ⋅ A.
Proof.
  intros hx hr.
  induction hr as [| ρ Γ i B h ih ho] in x, l, A, hx |- *.
  1: inversion hx.
  inversion hx. all: subst.
  - rasimpl. assumption.
  - rasimpl. apply ih. assumption.
Qed.

Lemma WellRen_comp Γ Δ Θ ρ ρ' :
  Δ ⊢r ρ : Θ →
  Γ ⊢r ρ' : Δ →
  Γ ⊢r (ρ >> ρ') : Θ.
Proof.
  intros hρ hρ'.
  induction hρ as [| ρ Θ i B h ih ho] in ρ', Γ, hρ' |- *.
  - constructor.
  - constructor.
    + eauto.
    + unfold ">>". eapply varty_meta.
      1: eauto using varty_ren.
      rasimpl. reflexivity.
Qed.

Lemma WellRen_id Γ :
  Γ ⊢r id : Γ.
Proof.
  induction Γ as [| [l A] Γ ih].
  - constructor.
  - constructor.
    + change (S >> id) with (id >> S).
      eauto using WellRen_weak.
    + constructor.
Qed.

Lemma WellRen_S Γ l A :
  Γ ,, (l, A) ⊢r S : Γ.
Proof.
  change S with (id >> S).
  apply WellRen_weak.
  apply WellRen_id.
Qed.

Lemma meta_conv Γ t l A B :
  Γ ⊢< l > t : A →
  A = B →
  Γ ⊢< l > t : B.
Proof.
  intros ? ->. auto.
Qed.

Lemma meta_conv_conv Γ u v l A B :
  Γ ⊢< l > u ≡ v : A →
  A = B →
  Γ ⊢< l > u ≡ v : B.
Proof.
  intros ? ->. auto.
Qed.

Lemma meta_rhs_conv Γ u v w l A :
  Γ ⊢< l > u ≡ v : A →
  v = w →
  Γ ⊢< l > u ≡ w : A.
Proof.
  intros ? ->. auto.
Qed.

Scheme typing_mut := Induction for typing Sort Prop
with conversion_mut := Induction for conversion Sort Prop.
Combined Scheme typing_mutind from typing_mut, conversion_mut.

Lemma validity_ctx :
  (∀ Γ l t A,
    Γ ⊢< l > t : A →
    ⊢ Γ
  ) ∧
  (∀ Γ l u v A,
    Γ ⊢< l > u ≡ v : A →
    ⊢ Γ).
Proof.
  apply typing_mutind. all: eauto.
Qed.

Corollary validity_ty_ctx Γ l t A :
    Γ ⊢< l > t : A →
    ⊢ Γ.
Proof.
  intros. eapply validity_ctx in H; eauto.
Qed.

Corollary validity_conv_ctx Γ l t u A :
    Γ ⊢< l > t ≡ u : A →
    ⊢ Γ.
Proof.
  intros. eapply validity_ctx in H; eauto.
Qed.


Ltac unfold_all_local :=
  repeat match goal with
  | H := ?rhs : ?ty |- _ => unfold H in *; clear H
  end.

Ltac meta_conv :=
  lazymatch goal with
  | |- _ ⊢< _ > _ : _ => eapply meta_conv
  | |- _ ⊢< _ > _ ≡ _ : _ => eapply meta_conv_conv
  end.

Lemma well_rcons_alt Γ Δ x ρ l A :
  Γ ⊢r ρ : Δ →
  Γ ∋< l > x : ρ ⋅ A →
  Γ ⊢r (x .: ρ) : Δ ,, (l , A).
Proof.
  intros hr hx.
  constructor.
  - erewrite autosubst_simpl_WellRen. 2: exact _.
    assumption.
  - cbn. rasimpl. assumption.
Qed.

Lemma varty0_eq Γ l A B :
  S ⋅ A = B →
  Γ ,, (l , A) ∋< l > 0 : B.
Proof.
  intros <-.
  constructor.
Qed.

Lemma vartyS_eq Γ i j A B C x :
  Γ ∋< i > x : A →
  S ⋅ A = C →
  Γ ,, (j, B) ∋< i > S x : C.
Proof.
  intros h <-.
  constructor. assumption.
Qed.

Create HintDb sidecond.

Hint Resolve
  WellRen_up WellRen_comp WellRen_S well_rcons_alt varty0_eq vartyS_eq
  ctx_nil ctx_cons
  : sidecond.

Hint Extern 100 (_ = _) =>
  rasimpl ; reflexivity : sidecond.

Lemma typing_conversion_ren :
  (∀ Γ l t A,
    Γ ⊢< l > t : A →
    ∀ Δ ρ,
      ⊢ Δ →
      Δ ⊢r ρ : Γ →
      Δ ⊢< l > ρ ⋅ t : ρ ⋅ A
  ) ∧
  (∀ Γ l u v A,
    Γ ⊢< l > u ≡ v : A →
    ∀ Δ ρ,
      ⊢ Δ →
      Δ ⊢r ρ : Γ →
      Δ ⊢< l > ρ ⋅ u ≡ ρ ⋅ v : ρ ⋅ A).
Proof.
  apply typing_mutind.

  (* solves most goals, which are easy *)
  all: try solve [ intros ; try econstructor ; eauto using varty_ren with sidecond ].

  (* solves remaining goals involving typing rules or congruence rules *)
  1-6,8-13 : solve [intros; cbn in *; meta_conv ;
            [ (econstructor ; eauto ; try solve [ meta_conv ;
              [ eauto 11 using WellRen_up, WellRen_meta, ctx_typing, typing, ctx_cons
              | rasimpl ; reflexivity]])
            | ssimpl; reflexivity]].

  (* solves all goals involving computation rules *)
  3-8: solve [ intros; cbn; eapply meta_conv_conv;
              [ eapply meta_rhs_conv;
                [ ((  eapply conv_beta + eapply conv_rec_zero + eapply conv_rec_succ +
                    eapply conv_J_refl + eapply conv_lower_lift + eapply conv_lift_lower +
                    eapply conv_pi1pair + eapply conv_pi2pair +
                    eapply conv_cast_univ + eapply conv_cast_nat + eapply conv_cast_pi) ;
                  eauto using ctx_typing, typing, WellRen_up; try (eapply meta_conv;
                  [ eauto 12 using ctx_typing, typing, WellRen_up
                  | rasimpl; reflexivity]))
                | ssimpl; reflexivity]
              | ssimpl; reflexivity] ].

  (* type_sum_case *)
  - intros **. cbn in *.
    meta_conv.
    { econstructor. all: eauto with sidecond.
      - eauto 7 using typing with sidecond.
      - meta_conv.
        { eauto using typing with sidecond. }
        rasimpl. apply ext_term. intros [].
        all: cbn. 2: reflexivity.
        rasimpl. reflexivity.
      - meta_conv.
        { eauto using typing with sidecond. }
        rasimpl. apply ext_term. intros [].
        all: cbn. 2: reflexivity.
        rasimpl. reflexivity.
    }
    rasimpl. reflexivity.

  (* conv_sum_case *)
  - intros **. cbn in *.
    meta_conv.
    { econstructor. all: eauto with sidecond.
      - eauto 7 using typing with sidecond.
      - meta_conv.
        { eauto using typing with sidecond. }
        rasimpl. apply ext_term. intros [].
        all: cbn. 2: reflexivity.
        rasimpl. reflexivity.
      - meta_conv.
        { eauto using typing with sidecond. }
        rasimpl. apply ext_term. intros [].
        all: cbn. 2: reflexivity.
        rasimpl. reflexivity.
    }
    rasimpl. reflexivity.

  (* conv_cast_pi *)
  - intros; eapply meta_conv_conv.
    + eapply meta_rhs_conv.
      * eapply conv_cast_pi; fold ren_term; try eapply meta_conv; try eassumption.        
        1,3,5,7,9,11:eauto 12 using ctx_typing, typing, WellRen_up.
        all:rasimpl;reflexivity.
      * fold ren_term. unfold_all_local. rasimpl. f_equal. f_equal. f_equal.  f_equal. rasimpl.  f_equal. f_equal; substify; asimpl; reflexivity.
    + fold ren_term. rasimpl. reflexivity.

  (* conv_sum_case_inl *)
  - intros **. cbn in *.
    meta_conv. 1: eapply meta_rhs_conv.
    { eapply conv_sum_case_inl. all: eauto 7 using typing with sidecond.
      - meta_conv.
        { eauto using typing with sidecond. }
        rasimpl. apply ext_term. intros [].
        all: cbn. 2: reflexivity.
        rasimpl. reflexivity.
      - meta_conv.
        { eauto using typing with sidecond. }
        rasimpl. apply ext_term. intros [].
        all: cbn. 2: reflexivity.
        rasimpl. reflexivity.
    }
    all: rasimpl. 1: reflexivity.
    apply ext_term. intros []. 2: reflexivity.
    rasimpl. reflexivity.

  (* conv_sum_case_inr *)
  - intros **. cbn in *.
    meta_conv. 1: eapply meta_rhs_conv.
    { eapply conv_sum_case_inr. all: eauto 7 using typing with sidecond.
      - meta_conv.
        { eauto using typing with sidecond. }
        rasimpl. apply ext_term. intros [].
        all: cbn. 2: reflexivity.
        rasimpl. reflexivity.
      - meta_conv.
        { eauto using typing with sidecond. }
        rasimpl. apply ext_term. intros [].
        all: cbn. 2: reflexivity.
        rasimpl. reflexivity.
    }
    all: rasimpl. 1: reflexivity.
    apply ext_term. intros []. 2: reflexivity.
    rasimpl. reflexivity.
Qed.

Lemma type_ren Γ l t A Δ ρ A' :
  Γ ⊢< l > t : A →
  ⊢ Δ →
  Δ ⊢r ρ : Γ →
  A' = ρ ⋅ A ->
  Δ ⊢< l > ρ ⋅ t : A'.
Proof.
  intros. subst. eapply typing_conversion_ren in H; eauto.
Qed.

Lemma conv_ren Γ l t u A Δ ρ A' :
  Γ ⊢< l > t ≡ u : A →
  ⊢ Δ →
  Δ ⊢r ρ : Γ →
  A' = ρ ⋅ A ->
  Δ ⊢< l > ρ ⋅ t ≡ ρ ⋅ u : A'.
Proof.
  intros. subst. eapply typing_conversion_ren in H; eauto.
Qed.

#[export] Instance WellSubst_morphism :
  Proper (eq ==> eq ==> (`=1`) ==> iff) WellSubst.
Proof.
  intros Γ ? <- Δ ? <- σ σ' e.
  revert σ σ' e. wlog_iff. intros σ σ' e h.
  induction h as [| σ Δ l A h ih ho] in σ', e |- *.
  - constructor.
  - constructor.
    + eapply ih. intros x. unfold ">>". apply e.
    + rewrite <- e. assumption.
Qed.

Lemma autosubst_simpl_WellSubst :
  ∀ Γ Δ r s,
    SubstSimplification r s →
    Γ ⊢s r : Δ ↔ Γ ⊢s s : Δ.
Proof.
  intros Γ Δ r s H.
  apply WellSubst_morphism. 1,2: auto.
  apply H.
Qed.

#[export] Hint Rewrite -> autosubst_simpl_WellSubst : rasimpl_outermost.

Lemma well_scons_alt Γ Δ σ u l A :
  Γ ⊢s σ : Δ →
  Γ ⊢< l > u : A <[ σ ] →
  Γ ⊢s (u .: σ) : Δ ,, (l, A).
Proof.
  intros hs hu.
  constructor.
  - erewrite autosubst_simpl_WellSubst. 2: exact _.
    assumption.
  - cbn. rasimpl. assumption.
Qed.

Lemma WellSubst_weak Γ Δ σ l A :
  Γ ⊢s σ : Δ →
  Γ ⊢< Ax l > A : Sort l ->
  Γ ,, (l, A) ⊢s (σ >> ren_term S) : Δ.
Proof.
  induction 1 as [| σ Δ i B h ih ho] in l, A |- *.
  - constructor.
  - constructor.
    + auto.
    + eapply meta_conv.
      * unfold ">>". eapply typing_conversion_ren. 1: eassumption.
        1:econstructor; eauto using validity_ty_ctx.
        eapply WellRen_S.
      * rasimpl. reflexivity.
Qed.

Lemma WellSubst_up Γ Δ l A A' σ :
  Γ ⊢s σ : Δ →
  A' = A <[ σ ] ->
  Γ ⊢< Ax l > A <[ σ ] : Sort l ->
  Γ ,, (l, A') ⊢s up_term σ : Δ ,, (l, A).
Proof.
  intros. subst.
  constructor.
  - rasimpl. apply WellSubst_weak; assumption.
  - rasimpl. cbn. econstructor.
    1: econstructor; eauto using validity_ty_ctx.
   eapply varty_meta.
    + constructor.
    + rasimpl. reflexivity.
Qed.

Lemma varty_subst Γ Δ σ x l A :
  Γ ∋< l > x : A →
  Δ ⊢s σ : Γ →
  Δ ⊢< l > σ x : A <[ σ ].
Proof.
  intros hx hs.
  induction hs as [| σ Γ i B h ih ho] in x, l, A, hx |- *.
  1: inversion hx.
  inversion hx. all: subst.
  - rasimpl. assumption.
  - rasimpl. apply ih. assumption.
Qed.

Lemma WellSubst_meta Γ Γ' Δ Δ' σ :
  Γ ⊢s σ : Δ →
  Γ = Γ' →
  Δ = Δ' →
  Γ' ⊢s σ : Δ'.
Proof.
  intros ? -> ->. auto.
Qed.

Lemma WellSubst_ren Γ Δ ρ :
  Δ ⊢r ρ : Γ →
  ⊢ Δ →
  Δ ⊢s (ρ >> var) : Γ.
Proof.
  induction 1.
  - constructor.
  - constructor.
    + eauto.
    + rasimpl. unfold ">>".
      econstructor. all: eassumption.
Qed.

Lemma WellSubst_compr Γ Δ Θ σ ρ :
  Δ ⊢s σ : Θ →
  Γ ⊢r ρ : Δ →
  ⊢ Γ →
  Γ ⊢s (σ >> ren_term ρ) : Θ.
Proof.
  intros hσ hρ hΓ.
  induction hσ as [| σ Θ i B h ih ho] in ρ, Γ, hΓ, hρ |- *.
  - constructor.
  - constructor.
    + eauto.
    + unfold ">>". meta_conv.
      { eapply type_ren. all: eauto. }
      rasimpl. reflexivity.
Qed.

Hint Resolve
  WellSubst_up WellSubst_weak well_scons_alt WellSubst_ren WellSubst_compr
  : sidecond.

Lemma typing_conversion_subst :
  (∀ Γ l t A,
    Γ ⊢< l > t : A →
    ∀ Δ σ,
      ⊢ Δ ->
      Δ ⊢s σ : Γ →
      Δ ⊢< l > t <[ σ ] : A <[ σ ]
  ) ∧
  (∀ Γ l u v A,
    Γ ⊢< l > u ≡ v : A →
    ∀ Δ σ,
      ⊢ Δ ->
      Δ ⊢s σ : Γ →
      Δ ⊢< l > u <[ σ ] ≡ v <[ σ ] : A <[ σ ]).
Proof.
  (* Basically copy-pasted from renaming *)
  apply typing_mutind; intros.

  (* solves goals involving variables *)
  1,28: solve [ cbn ; eauto using varty_subst, conv_refl ].

  (* solves most goals, which are easy *)
  all: try solve [ try econstructor ; eauto 8 using WellSubst_up, ctx_cons ].

  (* for the following parts, we will need this in the cases involving rec *)
  all: try assert (Δ,, (ty 0, Nat) ⊢< Ax l > P <[ up_term_term σ] : Sort l)
      by eauto 6 using ctx_typing, typing, WellSubst_meta, WellSubst_up.

  (* solves remaining goals involving typing rules or congruence rules *)
  1-6,8-13:solve [cbn in *; meta_conv ;
            [ (econstructor ; try eassumption ; try solve [ meta_conv ;
              [ eauto 11 using WellRen_up, WellSubst_up, WellSubst_meta, ctx_typing, typing, ctx_cons
              | rasimpl ; reflexivity]])
            | rasimpl; reflexivity]].

  (* solves all goals involving computation rules *)
  3-8:solve [ intros; cbn; eapply meta_conv_conv;
                [ eapply meta_rhs_conv;
                  [ ((eapply conv_beta + eapply conv_rec_zero + eapply conv_rec_succ +
                      eapply conv_J_refl + eapply conv_lower_lift + eapply conv_lift_lower +
                      eapply conv_pi1pair + eapply conv_pi2pair + eapply conv_sum_case_inl) ;
                    eauto using ctx_typing, typing, WellRen_up, WellSubst_up, WellSubst_meta; try (eapply meta_conv;
                    [ eauto 12 using ctx_typing, typing, WellRen_up, WellSubst_up, WellSubst_meta
                    | rasimpl; reflexivity]))
                  | rasimpl; reflexivity]
                | rasimpl; reflexivity] ].

  (* type_sum_case *)
  - cbn in *.
    meta_conv.
    { econstructor. all: eauto with sidecond.
      - eauto 10 using typing with sidecond.
      - meta_conv.
        { eauto 7 using typing with sidecond. }
        rasimpl. apply ext_term. intros [].
        all: cbn. 2: reflexivity.
        rasimpl. reflexivity.
      - meta_conv.
        { eauto 7 using typing with sidecond. }
        rasimpl. apply ext_term. intros [].
        all: cbn. 2: reflexivity.
        rasimpl. reflexivity.
    }
    rasimpl. reflexivity.

  (* conv_sum_case *)
  - cbn in *.
    meta_conv.
    { econstructor. all: eauto with sidecond.
      - eauto 10 using typing with sidecond.
      - meta_conv.
        { eauto 7 using typing with sidecond. }
        rasimpl. apply ext_term. intros [].
        all: cbn. 2: reflexivity.
        rasimpl. reflexivity.
      - meta_conv.
        { eauto 7 using typing with sidecond. }
        rasimpl. apply ext_term. intros [].
        all: cbn. 2: reflexivity.
        rasimpl. reflexivity.
    }
    rasimpl. reflexivity.

  (* conv_cast_pi *)
  - intros; eapply meta_conv_conv.
    + eapply meta_rhs_conv.
      * eapply conv_cast_pi; fold subst_term; try eassumption; eapply meta_conv.
        1,3,5,7,9,11:eauto 12 using ctx_typing, typing, WellRen_up, WellSubst_up, WellSubst_meta.
        all:rasimpl;reflexivity.
      * fold subst_term. unfold_all_local. rasimpl. f_equal. f_equal. f_equal.  f_equal. rasimpl.  f_equal.
    + fold subst_term. rasimpl. reflexivity.

  (* conv_sum_case_inl *)
  - cbn in *.
    meta_conv. 1: eapply meta_rhs_conv.
    { eapply conv_sum_case_inl. all: eauto 10 using typing with sidecond.
      - meta_conv.
        { eauto 7 using typing with sidecond. }
        rasimpl. apply ext_term. intros [].
        all: cbn. 2: reflexivity.
        rasimpl. reflexivity.
      - meta_conv.
        { eauto 7 using typing with sidecond. }
        rasimpl. apply ext_term. intros [].
        all: cbn. 2: reflexivity.
        rasimpl. reflexivity.
    }
    all: rasimpl. 1: reflexivity.
    apply ext_term. intros []. 2: reflexivity.
    rasimpl. reflexivity.

  (* conv_sum_case_inr *)
  - cbn in *.
    meta_conv. 1: eapply meta_rhs_conv.
    { eapply conv_sum_case_inr. all: eauto 10 using typing with sidecond.
      - meta_conv.
        { eauto 7 using typing with sidecond. }
        rasimpl. apply ext_term. intros [].
        all: cbn. 2: reflexivity.
        rasimpl. reflexivity.
      - meta_conv.
        { eauto 7 using typing with sidecond. }
        rasimpl. apply ext_term. intros [].
        all: cbn. 2: reflexivity.
        rasimpl. reflexivity.
    }
    all: rasimpl. 1: reflexivity.
    apply ext_term. intros []. 2: reflexivity.
    rasimpl. reflexivity.
Qed.


Theorem subst_ty Γ l t A Δ σ A' :
  ⊢ Δ ->
  Δ ⊢s σ : Γ ->
  Γ ⊢< l > t : A ->
  A' = A <[ σ ] ->
  Δ ⊢< l > t <[ σ ] : A'.
Proof.
  intros. subst. eapply typing_conversion_subst in H1; eauto.
Qed.


Theorem subst_id Γ :
  ⊢ Γ ->
  Γ ⊢s var : Γ.
Proof.
  induction Γ as [| (l, A) Γ ih].
  - constructor.
  - constructor.
    + eapply WellSubst_weak with (A := A) in ih; eauto.
      all:inversion H; eauto.
    + constructor; eauto. rasimpl. constructor.
Qed.

Lemma subst_one Γ l A u :
  Γ ⊢< l > u : A →
  Γ ⊢s u .. : Γ ,, (l, A).
Proof.
  intros h.
  apply well_scons_alt.
  - apply subst_id; eauto using validity_ty_ctx.
  - rasimpl. assumption.
Qed.

Lemma meta_lvl Γ t A i j :
  Γ ⊢< i > t : A →
  i = j →
  Γ ⊢< j > t : A.
Proof.
  intros ? ->. assumption.
Qed.

Lemma WellSubst_conv Γ Δ Ξ σ :
  Γ ⊢s σ : Δ →
  ⊢ Δ ≡ Ξ →
  Γ ⊢s σ : Ξ.
Proof.
  intros hs hc.
  induction hs as [| σ Δ l A hs ih h ] in Ξ, hc |- *.
  - inversion hc. constructor.
  - inversion hc. subst.
    constructor.
    + eapply ih. assumption.
    + eapply type_conv.
      * eassumption.
      * eapply meta_conv_conv.
        { eapply typing_conversion_subst. all: eauto using validity_ty_ctx. }
        reflexivity.
Qed.


(* We show weaker versions of conv_in_ctx in which we require the assumption ⊢ Δ.
  Once we have validity, we then prove the real conv_in_ctx which drop this assumption. *)
Lemma pre_conv_in_ctx_ty Γ Δ t l A :
  Γ ⊢< l > t : A →
  ⊢ Δ ->
  ⊢ Δ ≡ Γ →
  Δ ⊢< l > t : A.
Proof.
  intros h h' hc.
  eapply typing_conversion_subst with (σ := var) in h.
  - rasimpl in h. eassumption.
  - assumption.
  - eapply WellSubst_conv. 2: eassumption.
    apply subst_id. assumption.
Qed.

Lemma pre_conv_in_ctx_conv Γ Δ u v l A :
  Γ ⊢< l > u ≡ v : A →
  ⊢ Δ ->
  ⊢ Δ ≡ Γ →
  Δ ⊢< l > u ≡ v : A.
Proof.
  intros h h' hc.
  eapply typing_conversion_subst with (σ := var) in h.
  - rasimpl in h. eassumption.
  - assumption.
  - eapply WellSubst_conv. 2: eassumption.
    apply subst_id. assumption.
Qed.

Lemma valid_varty Γ x A l :
  ⊢ Γ →
  Γ ∋< l > x : A →
  Γ ⊢< Ax l > A : Sort l.
Proof.
  intros hΓ h.
  induction hΓ as [| Γ i B hΓ ih hB] in x, l, A, h |- *.
  1: inversion h.
  inversion h.
  - subst.
    eapply meta_conv.
    + eapply typing_conversion_ren. 3: eapply WellRen_S.
      1:eassumption. econstructor; eauto.
    + reflexivity.
  - subst.
    eapply meta_conv.
    + eapply typing_conversion_ren.
      2:econstructor; eauto.
    2: eapply WellRen_S.
      eapply ih. eassumption.
    + reflexivity.
Qed.

Lemma ctx_conv_refl Γ :
  ⊢ Γ →
  ⊢ Γ ≡ Γ.
Proof.
  induction 1 as [| Γ l A h ih hA].
  - constructor.
  - constructor. 1: assumption.
    apply conv_refl. assumption.
Qed.

#[export] Instance ConvSubst_morphism :
  Proper (eq ==> eq ==> (`=1`) ==> (`=1`) ==> iff) ConvSubst.
Proof.
  intros Γ ? <- Δ ? <- σ σ' e θ θ' e'.
  revert σ σ' e θ θ' e'. wlog_iff. intros σ σ' e θ θ' e' h.
  induction h as [| σ θ Δ l A h ih ho] in σ', e, θ', e' |- *.
  - constructor.
  - constructor.
    + eapply ih; unfold ">>". all: intro ; eauto.
    + rewrite <- e, <- e'. assumption.
Qed.

Lemma autosubst_simpl_ConvSubst :
  ∀ Γ Δ s1 s2 s3 s4,
    SubstSimplification s1 s2 →
    SubstSimplification s3 s4 →
    Γ ⊢s s1 ≡ s3 : Δ ↔ Γ ⊢s s2 ≡ s4 : Δ.
Proof.
  intros ?????? h1 h2.
  apply ConvSubst_morphism. 1,2: eauto.
  - apply h1.
  - apply h2.
Qed.

#[export] Hint Rewrite -> autosubst_simpl_ConvSubst : rasimpl_outermost.

Lemma conv_scons_alt Γ Δ σ θ u v l A :
  Γ ⊢s σ ≡ θ : Δ →
  Γ ⊢< l > u ≡ v : A <[ σ ] →
  Γ ⊢s (u .: σ) ≡ (v .: θ) : Δ ,, (l, A).
Proof.
  intros hs hu.
  constructor.
  - erewrite autosubst_simpl_ConvSubst. 2,3: exact _.
    assumption.
  - cbn. rasimpl. assumption.
Qed.

Lemma ConvSubst_weak Γ Δ σ θ l A :
  Γ ⊢s σ ≡ θ : Δ →
  Γ ⊢< Ax l > A : Sort l ->
  Γ ,, (l, A) ⊢s (σ >> ren_term S) ≡ (θ >> ren_term S) : Δ.
Proof.
  induction 1 as [| σ θ Δ i B h ih ho] in l, A |- *.
  - constructor.
  - constructor.
    + auto.
    + eapply meta_conv_conv.
      * unfold ">>". eapply typing_conversion_ren. 1: eassumption.
        1: econstructor; eauto using validity_ty_ctx.
        eapply WellRen_S.
      * rasimpl. reflexivity.
Qed.

Lemma conv_substs_up Γ Δ σ σ' l A :
  Γ ⊢s σ ≡ σ' : Δ →
  Γ ⊢< Ax l > A <[ σ ] : Sort l ->
  Γ ,, (l, A <[ σ ]) ⊢s up_term σ ≡ up_term σ' : Δ ,, (l, A).
Proof.
  intros h h'.
  apply conv_scons_alt.
  - apply ConvSubst_weak; assumption.
  - constructor. 1:econstructor; eauto using validity_ty_ctx.
    eapply varty_meta.
    + constructor.
    + rasimpl. reflexivity.
Qed.

Theorem substs_id Γ :
  ⊢ Γ ->
  Γ ⊢s var ≡ var : Γ.
Proof.
  intros.
  induction Γ as [| (l, A) Γ ih].
  - constructor.
  - constructor.
    + inversion H. eapply ConvSubst_weak with (A := A) in ih.
      all:eassumption.
    + constructor. 1:eauto. rasimpl. constructor.
Qed.

Lemma substs_one Γ l A u v :
  Γ ⊢< l > u ≡ v : A →
  Γ ⊢s u .. ≡ v .. : Γ ,, (l, A).
Proof.
  intros h.
  apply conv_scons_alt.
  - apply substs_id. eauto using validity_conv_ctx.
  - rasimpl. assumption.
Qed.

Lemma varty_conv_substs Γ Δ σ θ x l A :
  Γ ∋< l > x : A →
  Δ ⊢s σ ≡ θ : Γ →
  Δ ⊢< l > σ x ≡ θ x : A <[ σ ].
Proof.
  intros hx hs.
  induction hs as [| σ θ Γ i B h ih ho] in x, l, A, hx |- *.
  1: inversion hx.
  inversion hx. all: subst.
  - rasimpl. assumption.
  - rasimpl. apply ih. assumption.
Qed.

Lemma subst_conv_meta_conv_ctx Γ Δ σ τ Γ' :
  Γ ⊢s σ ≡ τ : Δ ->
  Γ = Γ' ->
  Γ' ⊢s σ ≡ τ : Δ.
Proof.
  intros. subst. assumption.
Qed.

Lemma subst_meta_conv_ctx Γ Δ σ Γ' :
  Γ ⊢s σ : Δ ->
  Γ = Γ' ->
  Γ' ⊢s σ : Δ.
Proof.
  intros. subst. assumption.
Qed.

(* Lemmas to reduce size of proofs *)

Notation "Γ ⊢⊢< l > t : A" :=
  (⊢ Γ → Γ ⊢< l > t : A)
  (at level 50, l, t, A at next level).

Notation "Γ ⊢⊢< l > u ≡ v : A" :=
  (⊢ Γ → Γ ⊢< l > u ≡ v : A)
  (at level 50, l, u, v, A at next level).

Lemma wf_conv_sum_case Γ i j l A A' B B' P P' pl pl' pr pr' t t' :
  Γ ⊢< Ax (ty i) > A : Sort (ty i) →
  Γ ⊢< Ax (ty j) > B : Sort (ty j) →
  Γ ⊢< Ax (ty i) > A ≡ A' : Sort (ty i) →
  Γ ⊢< Ax (ty j) > B ≡ B' : Sort (ty j) →
  (Γ ⊢< Ax (ty (max i j)) > tysum (ty i) (ty j) A B : Sort (ty (max i j)) →
  Γ ,, (ty (max i j), tysum (ty i) (ty j) A B) ⊢⊢< Ax l > P ≡ P' : Sort l) →
  (Γ ⊢< Ax (ty i) > A : Sort (ty i) →
  Γ ,, (ty i, A) ⊢⊢< l > pl ≡ pl' : P <[ (inl (ty i) (ty j) (S ⋅ A) (S ⋅ B) (var 0)) .: S >> var ]) →
  (Γ ⊢< Ax (ty j) > B : Sort (ty j) →
  Γ ,, (ty j, B) ⊢⊢< l > pr ≡ pr' : P <[ (inr (ty i) (ty j) (S ⋅ A) (S ⋅ B) (var 0)) .: S >> var ]) →
  Γ ⊢< ty (max i j) > t ≡ t' : tysum (ty i) (ty j) A B →
  Γ ⊢< l > sum_case (ty i) (ty j) l A B P pl pr t ≡ sum_case (ty i) (ty j) l A' B' P' pl' pr' t' : P <[ t .. ].
Proof.
  intros **.
  econstructor. all: eauto 7 using validity_ty_ctx, ctx_cons, typing.
Qed.

Lemma conv_substs Γ Δ σ σ' t l A :
  ⊢ Δ ->
  Δ ⊢s σ ≡ σ' : Γ →
  Δ ⊢s σ : Γ →
  Γ ⊢< l > t : A →
  Δ ⊢< l > t <[ σ ] ≡ t <[ σ' ] : A <[ σ ].
Proof.
  intros h hs hst ht.
  induction ht in Δ, σ, σ', h, hs, hst |- *; cbn.

  all: try solve  [cbn in *; meta_conv ;
            [ (econstructor ; eauto ; try solve [ meta_conv ;
              [ eauto 11 using conv_substs_up, WellSubst_up, ctx_typing, subst_ty
              | rasimpl ; reflexivity]])
            | rasimpl; reflexivity]].

  - eauto using varty_conv_substs.
  - assert (Δ,, (ty 0, Nat) ⊢< Ax l > P <[ up_term_term σ] : Sort l)
      by (eapply typing_conversion_subst in ht1; eauto using typing, ctx_typing, WellSubst_up).
    eapply meta_conv_conv.
    + econstructor.
          all : try solve [ meta_conv ; [
        eauto 12 using ctx_typing, typing, WellSubst_up, conv_substs_up, subst_conv_meta_conv_ctx, subst_meta_conv_ctx | rasimpl ; reflexivity]].
    + rasimpl; reflexivity.
  - meta_conv.
    { eapply wf_conv_sum_case. all: intros. all: eauto with sidecond.
      1,2: meta_conv ; [ eapply typing_conversion_subst | ] ; eauto with sidecond.
      - meta_conv.
        { eapply IHht3. all: eauto using typing, conv_substs_up with sidecond.
          eapply conv_substs_up with (A := tysum _ _ _ _). all: eauto.
        }
        reflexivity.
      - meta_conv.
        { eauto using typing, conv_substs_up with sidecond. }
        rasimpl. apply ext_term. intros []. 2: reflexivity.
        rasimpl. reflexivity.
      - meta_conv.
        { eauto using typing, conv_substs_up with sidecond. }
        rasimpl. apply ext_term. intros []. 2: reflexivity.
        rasimpl. reflexivity.
    }
    rasimpl. reflexivity.
  - eapply conv_conv. 1: eauto.
    eapply meta_conv_conv.
    + eapply typing_conversion_subst; eauto. all: eauto.
    + reflexivity.
Qed.


Theorem pre_subst_conv Γ l t u A Δ σ τ A' :
  ⊢ Δ ->
  Δ ⊢s σ : Γ ->
  Δ ⊢s σ ≡ τ : Γ ->
  Γ ⊢< l > t : A ->
  Γ ⊢< l > u : A ->
  Γ ⊢< l > t ≡ u : A ->
  A' = A <[ σ ] ->
  Δ ⊢< l > t <[ σ ] ≡ u <[ τ ] : A'.
Proof.
  intros. subst.
  eapply conv_trans.
  1:eapply typing_conversion_subst in H4; eauto.
  eapply conv_substs; eauto.
Qed.


Lemma pre_conv_ty_in_ctx_ty Γ l A A' l' t B :
  Γ ,, (l , A) ⊢< l' > t : B ->
  Γ ⊢< Ax l > A' : Sort l ->
  Γ ⊢< Ax l > A ≡ A' : Sort l ->
  Γ ,, (l , A') ⊢< l' > t : B.
Proof.
  intros t_eq_u A'Wt A_eq_A'.
  eapply pre_conv_in_ctx_ty; eauto using ctx_typing, validity_ty_ctx.
  apply conv_ccons; eauto using ctx_conv_refl, validity_ty_ctx, conv_sym, ctx_conv_refl.
Qed.

Lemma pre_conv_ty_in_ctx_conv Γ l A A' l' t t' B :
  Γ ,, (l , A) ⊢< l' > t ≡ t' : B ->
  Γ ⊢< Ax l > A' : Sort l ->
  Γ ⊢< Ax l > A ≡ A' : Sort l ->
  Γ ,, (l , A') ⊢< l' > t ≡ t' : B.
Proof.
  intros t_eq_u A'Wt A_eq_A'.
  eapply pre_conv_in_ctx_conv; eauto using ctx_typing, validity_ty_ctx.
  apply conv_ccons; eauto using ctx_conv_refl, validity_ty_ctx, conv_sym, ctx_conv_refl.
Qed.

Ltac validitysplit :=
  intros ; split ; [
    eapply meta_conv ; [ eapply meta_lvl ;  [ econstructor | idtac ] | idtac ] |
    eapply type_conv ; [ eapply meta_lvl ; [ econstructor | idtac ] | idtac ]
  ].

Hint Resolve
  validity_ty_ctx
  : sidecond.

Lemma validity_gen :
  (∀ Γ l t A,
    Γ ⊢< l > t : A →
    Γ ⊢< Ax l > A : Sort l
  ) ∧
  (∀ Γ l u v A,
    Γ ⊢< l > u ≡ v : A →
    Γ ⊢< l > u : A ∧ Γ ⊢< l > v : A).
Proof.
  apply typing_mutind.

  (* 6,7,8,9,25,26,27,28,41,42:shelve. *)

  all:try solve [intuition eauto 5 using conversion, typing, validity_ty_ctx, valid_varty, meta_lvl, pre_conv_ty_in_ctx_ty, subst_ty, subst_one].

  (* cases type_pi1, conv_refl, conv_lift and conv_lower *)
  5,8,10,11: solve [intuition eauto 7 using conversion, typing, validity_ty_ctx,  valid_varty, meta_lvl, pre_conv_ty_in_ctx_ty, subst_ty, subst_one].


  (* cases conv_lam, conv_app, conv_sigma, conv_J and conv_cast *)
  2-4,7,8: solve [validitysplit; intuition eauto 6 using typing, conversion, pre_conv_in_ctx_ty, conv_sym, pre_conv_ty_in_ctx_ty, pre_subst_conv, validity_ty_ctx, subst_one, substs_one].



  (* the remaining cases are too hard to be solved by automation *)


  (* type_cast_pi1 *)
  - intuition eauto. econstructor; eauto using typing, validity_ty_ctx, subst_ty, subst_one.
    eapply subst_ty; eauto using validity_ty_ctx.
    eapply subst_one. econstructor; eauto. econstructor; eauto.

  (* conv_pi2 *)
  - intuition eauto using typing.
    eapply type_conv.
    + econstructor; eauto using typing, conversion, pre_conv_ty_in_ctx_ty.
    + eapply pre_subst_conv; eauto using validity_ty_ctx, conversion.
      * eapply subst_one; eauto 7 using typing, conversion, pre_conv_ty_in_ctx_ty.
      * eapply substs_one; eauto 7 using typing, conversion, pre_conv_ty_in_ctx_ty.

  (* conv_rec *)
  - intros Γ l P **.
    split.
    + econstructor. all: intuition eauto.
    + eapply type_conv.
      * {
        econstructor. all: intuition eauto.
        - eapply type_conv. 1: intuition eauto.
          eapply meta_conv_conv.
          + eapply typing_conversion_subst. 1,2: intuition eauto using validity_ty_ctx.
            eapply well_scons_alt.
            * apply subst_id. eauto using validity_ty_ctx.
            * cbn. constructor. eauto using validity_ty_ctx.
          + reflexivity.
        - eapply pre_conv_in_ctx_ty.
          + eapply type_conv. 1: intuition eauto.
            eapply meta_conv_conv.
            * {
              eapply typing_conversion_subst. 1: intuition eauto.
              1:econstructor; eauto using validity_ty_ctx.
              eapply well_scons_alt.
              - change (↑ >> (↑ >> var)) with (var >> ren_term S >> ren_term S).
                eapply WellSubst_weak.
                1:eapply WellSubst_weak.
                1:apply subst_id; eauto using validity_ty_ctx.
                1,2:eauto using typing, validity_ty_ctx.
              - cbn. constructor.
                eapply meta_conv.
                + repeat constructor. all:eauto using validity_ty_ctx.
                + reflexivity.
            }
            * reflexivity.
          + constructor. 1: eauto using ctx_conv_refl, validity_ty_ctx. eauto.
          + econstructor; eauto using ctx_conv_refl, conv_sym, validity_ty_ctx.
      }
      * {
        apply conv_sym. eapply conv_trans.
        - eapply meta_conv_conv.
          + eapply typing_conversion_subst.
            all: intuition eauto using subst_one, validity_ty_ctx.
          + reflexivity.
        - eapply meta_conv_conv.
          { eapply conv_substs.
            - eauto using validity_conv_ctx.
            - eapply substs_one. eauto.
            - eapply subst_one. intuition eauto.
            - intuition eauto.
          }
          reflexivity.
      }

  (* conv_injpi1 *)
  - intuition eauto. 1:econstructor;eauto.
    eapply type_conv.
    1:econstructor; eauto using pre_conv_ty_in_ctx_ty.
    1:eapply type_conv; eauto.
    all:econstructor; eauto using conv_sym, conversion, validity_ty_ctx.

  (* conv_injpi2 *)
  - intuition eauto. split. 1:econstructor;eauto.
    eapply type_conv.
    1:econstructor; eauto using pre_conv_ty_in_ctx_ty, type_conv.
    1:eapply type_conv; eauto.
    all:econstructor; eauto using conv_sym, conversion, validity_ty_ctx.
    all:eapply pre_subst_conv; eauto using validity_ty_ctx, subst_one, substs_one, conv_sym.
    + eapply subst_one. eapply type_conv. 1:econstructor; eauto using typing.
      2:eauto using conv_sym.
      econstructor; eauto using pre_conv_ty_in_ctx_ty.
      eapply type_conv; eauto.
      econstructor; eauto using conversion, validity_ty_ctx.
    + eapply substs_one. eapply conv_conv. 1:econstructor; eauto using conversion.
      2:eauto using conv_sym.
      econstructor; eauto using pre_conv_ty_in_ctx_conv, conv_sym.
      eapply conv_conv ; eauto using conv_sym.
      econstructor; eauto using conversion, validity_ty_ctx.

  (* conv_inl *)
  - intuition idtac. 1: econstructor ; eauto.
    econstructor.
    { econstructor. all: eauto.
      econstructor. all: eauto.
    }
    apply conv_sym. econstructor. all: eauto.

  (* conv_inr *)
  - intuition idtac. 1: econstructor ; eauto.
    econstructor.
    { econstructor. all: eauto.
      econstructor. all: eauto.
    }
    apply conv_sym. econstructor. all: eauto.

  (* conv_sum_case *)
  - intuition idtac. 1: econstructor ; eauto.
    econstructor.
    { econstructor. all: eauto using pre_conv_ty_in_ctx_ty, typing, conversion.
      - eapply pre_conv_ty_in_ctx_ty. all: eauto using typing, conversion.
        econstructor. 1: eassumption.
        meta_conv.
        { eapply pre_subst_conv.
          all: eauto with sidecond.
          - apply well_scons_alt.
            + eauto with sidecond.
            + rasimpl. econstructor.
              * meta_conv.
                { eapply typing_conversion_ren. all: eauto with sidecond. }
                reflexivity.
              * meta_conv.
                { eapply typing_conversion_ren. all: eauto with sidecond. }
                reflexivity.
              * econstructor. all: eauto with sidecond.
          - apply conv_scons_alt.
            + apply refl_subst. eauto with sidecond.
            + rasimpl. econstructor.
              * meta_conv.
                { eapply typing_conversion_ren. all: eauto with sidecond. }
                reflexivity.
              * meta_conv.
                { eapply typing_conversion_ren. all: eauto with sidecond. }
                reflexivity.
              * eauto using typing, conversion with sidecond.
        }
        reflexivity.
      - eapply pre_conv_ty_in_ctx_ty. all: eauto using typing, conversion.
        econstructor. 1: eassumption.
        meta_conv.
        { eapply pre_subst_conv.
          all: eauto with sidecond.
          - apply well_scons_alt.
            + eauto with sidecond.
            + rasimpl. econstructor.
              * meta_conv.
                { eapply typing_conversion_ren. all: eauto with sidecond. }
                reflexivity.
              * meta_conv.
                { eapply typing_conversion_ren. all: eauto with sidecond. }
                reflexivity.
              * econstructor. all: eauto with sidecond.
          - apply conv_scons_alt.
            + apply refl_subst. eauto with sidecond.
            + rasimpl. econstructor.
              * meta_conv.
                { eapply typing_conversion_ren. all: eauto with sidecond. }
                reflexivity.
              * meta_conv.
                { eapply typing_conversion_ren. all: eauto with sidecond. }
                reflexivity.
              * eauto using typing, conversion with sidecond.
        }
        reflexivity.
    }
    apply conv_sym. meta_conv.
    { eapply pre_subst_conv.
      all: eauto using subst_one, substs_one with sidecond.
    }
    reflexivity.

  (* conv_pi2pair *)
  - intuition eauto.
    eapply type_conv.
    1:eauto using typing.
    eapply pre_subst_conv; eauto using validity_ty_ctx, conv_refl, subst_one, substs_one, typing, conversion.

  (* conv_recsucc *)
  - intros Γ l P **.
    split.
    + econstructor. all: intuition eauto.
      econstructor. auto.
    + eapply meta_conv.
      { eapply typing_conversion_subst.
        - eauto using validity_ty_ctx.
        - eauto using validity_ty_ctx.
        - eapply well_scons_alt.
          + apply subst_one. assumption.
          + econstructor. all: intuition eauto.
      }
      rasimpl. reflexivity.

  (* conv_cast_pi *)
  - intuition eauto. split.
    + econstructor; eauto using typing.
    + econstructor; eauto.
      assert (Γ ,, (i, A2) ⊢< i > cast i (S ⋅ A2) (S ⋅ A1) (injpi1 i (ty n) (S ⋅ A1) (S ⋅ A2) (up_ren S ⋅ B1) (up_ren S ⋅ B2) (S ⋅ e)) (var 0) : S ⋅ A1).
      { econstructor. 1:eassumption.
        ** eapply type_ren; eauto using WellRen_S.
           econstructor; eauto using validity_ty_ctx.
        ** eapply type_ren; eauto using WellRen_S.
           econstructor; eauto using validity_ty_ctx.
        ** econstructor. 1:eassumption.
           1-4:eapply type_ren; eauto using WellRen_S.
           1,2,4,5:econstructor; eauto using validity_ty_ctx.
           1,2:eapply type_ren; eauto using WellRen_S.
           1,2:econstructor; eauto using validity_ty_ctx.
           1,2:eapply WellRen_up; eauto using WellRen_S.
           eapply type_ren; eauto using WellRen_S.
           econstructor; eauto using validity_ty_ctx.
        ** eapply meta_conv. 1:econstructor. 2:econstructor.
           1:econstructor; eauto using validity_ty_ctx. reflexivity. }
      econstructor; eauto.
      * eapply subst_ty; eauto using validity_ty_ctx, ctx_typing.
        econstructor.
        ** ssimpl. change (S >> var) with (var >> ren_term S). eapply WellSubst_weak; eauto using subst_id, validity_ty_ctx.
        ** ssimpl. rasimpl. eassumption.
      * eapply meta_conv.
        1:econstructor; eauto 7 using type_ren, WellRen_S, validity_ty_ctx, WellRen_up, type_ren, ctx_typing.
        1:econstructor; eauto using ctx_typing, validity_ty_ctx, varty.
        rasimpl; f_equal. replace B2 with (B2 <[var]) at 2. 2:rasimpl;reflexivity.
        eapply subst_term_morphism; eauto.
        unfold pointwise_relation. intro a;destruct a; reflexivity.

      * eapply meta_conv.
        1:econstructor; eauto.
        1-3:eapply type_ren; eauto using WellRen_S, ctx_typing, validity_ty_ctx, WellRen_up, type_ren.
        rasimpl; reflexivity.

  (* conv_sum_case_inl *)
  - intuition idtac. 1: eauto using typing with sidecond.
    meta_conv.
    { eapply typing_conversion_subst. all: eauto using subst_one with sidecond. }
    rasimpl. apply ext_term. intros.
    rasimpl. reflexivity.

  (* conv_sum_case_inr *)
  - intuition idtac. 1: eauto using typing with sidecond.
    meta_conv.
    { eapply typing_conversion_subst. all: eauto using subst_one with sidecond. }
    rasimpl. apply ext_term. intros.
    rasimpl. reflexivity.
Qed.

Theorem validity_conv_left Γ l t u A :
  Γ ⊢< l > t ≡ u : A ->
  Γ ⊢< l > t : A.
Proof.
  intros. eapply validity_gen in H as (H1 & H2); eauto.
Qed.

Theorem validity_conv_right Γ l t u A :
  Γ ⊢< l > t ≡ u : A ->
  Γ ⊢< l > u : A.
Proof.
  intros. eapply validity_gen in H as (H1 & H2); eauto.
Qed.

Theorem validity_ty_ty Γ l t A :
  Γ ⊢< l > t : A ->
  Γ ⊢< Ax l > A : Sort l.
Proof.
  intros.
  eapply validity_gen in H. assumption.
Qed.

Lemma validity_subst_conv_left Δ Γ σ τ :
  Δ ⊢s σ ≡ τ : Γ ->
  Δ ⊢s σ : Γ.
Proof.
  intros. induction H; eauto using validity_conv_left, WellSubst.
Qed.

Lemma subst_sym Δ Γ σ τ :
  ⊢ Δ ->
  ⊢ Γ ->
  Δ ⊢s σ ≡ τ : Γ ->
  Δ ⊢s τ ≡ σ : Γ.
Proof.
  intros. induction H1; eauto using ConvSubst.
  econstructor; dependent destruction H0; eauto.
  eapply conv_sym. eapply conv_conv. 1:eauto.
  eapply conv_substs in H1; eauto using validity_subst_conv_left.
  eauto.
Qed.


Lemma validity_subst_conv_right Δ Γ σ τ :
  ⊢ Δ ->
  ⊢ Γ ->
  Δ ⊢s σ ≡ τ : Γ ->
  Δ ⊢s τ : Γ.
Proof.
  intros. eapply subst_sym in H1; eauto. eapply validity_subst_conv_left; eauto.
Qed.




Theorem subst_conv Γ l t u A Δ σ τ A' :
  ⊢ Δ ->
  Δ ⊢s σ ≡ τ : Γ ->
  Γ ⊢< l > t ≡ u : A ->
  A' = A <[ σ ] ->
  Δ ⊢< l > t <[ σ ] ≡ u <[ τ ] : A'.
Proof.
  intros. eauto using pre_subst_conv, validity_conv_left, validity_conv_right, validity_subst_conv_left.
Qed.


Lemma validity_ctx_conv_left Γ Δ :
  ⊢ Γ ≡ Δ ->
  ⊢ Γ.
Proof.
  intros. induction H.
  - econstructor.
  - econstructor; eauto using validity_conv_left.
Qed.


Lemma ctx_conv_sym Γ Δ :
  ⊢ Γ ≡ Δ ->
  ⊢ Δ ≡ Γ.
Proof.
  intros. induction H.
  - econstructor.
  - econstructor; eauto.
    eapply conv_sym in H0.
    eapply pre_conv_in_ctx_conv; eauto using validity_ctx_conv_left.
Qed.


Lemma validity_ctx_conv_right Γ Δ :
  ⊢ Γ ≡ Δ ->
  ⊢ Δ.
Proof.
  intros. eauto using ctx_conv_sym, validity_ctx_conv_left.
Qed.



Theorem conv_in_ctx_ty Γ Δ l t A :
  ⊢ Γ ≡ Δ ->
  Γ ⊢< l > t : A ->
  Δ ⊢< l > t : A.
Proof.
  intros.
  eapply pre_conv_in_ctx_ty; eauto using validity_ctx_conv_right, ctx_conv_sym.
Qed.

Theorem conv_in_ctx_conv Γ Δ l t u A :
  ⊢ Γ ≡ Δ ->
  Γ ⊢< l > t ≡ u : A ->
  Δ ⊢< l > t ≡ u : A.
Proof.
  intros.
  eapply pre_conv_in_ctx_conv; eauto using validity_ctx_conv_right, ctx_conv_sym.
Qed.



(* composite lemmas, for helping automation *)

Lemma conv_ty_in_ctx_conv Γ l A A' l' t u B :
  Γ ,, (l , A) ⊢< l' > t ≡ u : B ->
  Γ ⊢< Ax l > A ≡ A' : Sort l ->
  Γ ,, (l , A') ⊢< l' > t ≡ u : B.
Proof.
  intros t_eq_u A_eq_A'.
  eapply conv_in_ctx_conv; eauto.
  apply conv_ccons; eauto using ctx_conv_refl, validity_ty_ctx, validity_conv_left.
Qed.

Lemma conv_ty_in_ctx_ty Γ l A A' l' t B :
  Γ ,, (l , A) ⊢< l' > t : B ->
  Γ ⊢< Ax l > A ≡ A' : Sort l ->
  Γ ,, (l , A') ⊢< l' > t : B.
Proof.
  intros. eauto using pre_conv_ty_in_ctx_ty, validity_conv_right.
Qed.

(* the following lemma helps automation to type some substitutions that appear often in the proof *)
Lemma subst_id_var1 Γ l P :
  Γ ,, (ty 0, Nat) ⊢< Ax l > P : Sort l ->
  (Γ,, (ty 0, Nat)),, (l, P) ⊢s (succ (var 1) .: ↑ >> (↑ >> var)) : Γ ,, (ty 0, Nat).
Proof.
  intro H.
  apply well_scons.
  - ssimpl.
    change (↑ >> (↑ >> var)) with ((var >> ren_term ↑) >> ren_term ↑).
    eapply WellSubst_weak; eauto.
    eapply validity_ty_ctx in H. dependent destruction H.
    eapply WellSubst_weak; eauto using subst_id.
  - ssimpl. apply type_succ. apply (type_var _ 1 _ Nat); eauto.
    all:eauto using validity_ty_ctx, ctx_cons.
    eapply (vartyS _ _ _ Nat _ 0). eapply vartyO.
Qed.

(* Type inversion *)
Inductive type_inv_data : ctx -> level -> term -> term -> Prop :=
  | inv_data_var Γ l x A T
    (var_in_ctx : Γ ∋< l > x : A)
    (conv_ty : Γ ⊢< Ax l > T ≡ A : Sort l)
    : type_inv_data Γ l (var x) T
  | inv_data_sort Γ l i T
    (lvl_eq : l = Ax (Ax i))
    (conv_ty : Γ ⊢< Ax (Ax (Ax i)) > T ≡ Sort (Ax i) : Sort (Ax (Ax i)))
    : type_inv_data Γ l (Sort i) T
  | inv_data_pi Γ l A B i j T
    (A_Wt : Γ ⊢< Ax i > A : Sort i)
    (B_Wt : Γ ,, (i, A) ⊢< Ax j > B : Sort j)
    (lvl_eq : l = Ax (Ru i j))
    (conv_ty : Γ ⊢< Ax (Ax (Ru i j)) > T ≡ Sort (Ru i j) : Sort (Ax (Ru i j)))
    : type_inv_data Γ l (Pi i j A B) T
  | inv_data_lam Γ l A B t i j T
    (A_Wt : Γ ⊢< Ax i > A : Sort i)
    (B_Wt : Γ ,, (i, A) ⊢< Ax j > B : Sort j)
    (t_Wt : Γ ,, (i , A) ⊢< j > t : B)
    (lvl_eq : l = Ru i j)
    (conv_ty : Γ ⊢< Ax (Ru i j) > T ≡ Pi i j A B : Sort (Ru i j))
    : type_inv_data Γ l (lam i j A B t) T
  | inv_data_app Γ A B t u i j T l
    (A_Wt : Γ ⊢< Ax i > A : Sort i)
    (B_Wt : Γ ,, (i, A) ⊢< Ax j > B : Sort j)
    (t_Wt : Γ ⊢< Ru i j > t : Pi i j A B)
    (u_Wt : Γ ⊢< i > u : A)
    (lvl_eq : l = j)
    (conv_ty : Γ ⊢< Ax j > T ≡ B <[ u.. ] : Sort j)
    : type_inv_data Γ l (app i j A B t u) T
  | inv_data_sigma Γ l A B i j n m T
    (A_Wt : Γ ⊢< Ax (ty n) > A : Sort (ty n))
    (B_Wt : Γ ,, (ty n, A) ⊢< Ax (ty m) > B : Sort (ty m))
    (lvl_eq : l = Ax (ty (max n m)))
    (lvl_eq_i : i = ty n)
    (lvl_eq_j : j = ty m)
    (conv_ty : Γ ⊢< Ax (Ax (ty (max n m))) > T ≡ Sort (ty (max n m)) : Sort (Ax (ty (max n m))))
    : type_inv_data Γ l (Sigma i j A B) T
  | inv_data_pair Γ l A B a b i j n m T
    (A_Wt : Γ ⊢< Ax (ty n) > A : Sort (ty n))
    (B_Wt : Γ ,, (ty n, A) ⊢< Ax (ty m) > B : Sort (ty m))
    (a_Wt : Γ ⊢< ty n > a : A)
    (b_Wt : Γ ⊢< ty m > b : B<[a..])
    (lvl_eq : l = ty (max n m))
    (lvl_eq_i : i = ty n)
    (lvl_eq_j : j = ty m)
    (conv_ty : Γ ⊢< Ax (ty (max n m)) > T ≡ Sigma (ty n) (ty m) A B : Sort (ty (max n m)))
    : type_inv_data Γ l (pair i j A B a b) T
  | inv_data_pi1 Γ l A B t i j n m T
    (A_Wt : Γ ⊢< Ax (ty n) > A : Sort (ty n))
    (B_Wt : Γ ,, (ty n, A) ⊢< Ax (ty m) > B : Sort (ty m))
    (t_Wt : Γ ⊢< ty (max n m) > t : Sigma (ty n) (ty m) A B)
    (lvl_eq : l = ty n)
    (lvl_eq_i : i = ty n)
    (lvl_eq_j : j = ty m)
    (conv_ty : Γ ⊢< Ax (ty n) > T ≡ A : Sort (ty n))
    : type_inv_data Γ l (pi1 i j A B t) T
  | inv_data_pi2 Γ l A B t i j n m T
    (A_Wt : Γ ⊢< Ax (ty n) > A : Sort (ty n))
    (B_Wt : Γ ,, (ty n, A) ⊢< Ax (ty m) > B : Sort (ty m))
    (t_Wt : Γ ⊢< ty (max n m) > t : Sigma (ty n) (ty m) A B)
    (lvl_eq : l = ty m)
    (lvl_eq_i : i = ty n)
    (lvl_eq_j : j = ty m)
    (conv_ty : Γ ⊢< Ax (ty m) > T ≡ B<[(pi1 (ty n) (ty m) A B t)..] : Sort (ty m))
    : type_inv_data Γ l (pi2 i j A B t) T
  | inv_data_Nat Γ l T
    (lvl_eq : l = ty 1)
    (conv_ty : Γ ⊢< ty 2 > T ≡ Sort (ty 0) : Sort (ty 1))
    : type_inv_data Γ l Nat T
  | type_inv_zero l Γ T
    (lvl_eq : l = ty 0)
    (conv_ty : Γ ⊢< ty 1 > T ≡ Nat : Sort (ty 0))
    : type_inv_data Γ l zero T
  | type_inv_succ Γ l t T
    (t_Wt : Γ ⊢< ty 0 > t : Nat)
    (lvl_eq : l = ty 0)
    (conv_ty : Γ ⊢< ty 1 > T ≡ Nat : Sort (ty 0))
    : type_inv_data Γ l (succ t) T
  | type_inv_rec Γ l i P p_zero p_succ t T
    (P_Wt : Γ ,, (ty 0 , Nat) ⊢< Ax i > P : Sort i)
    (p_zero_Wt : Γ ⊢< i > p_zero : P <[ zero .. ])
    (p_succ_Wt : Γ ,, (ty 0 , Nat) ,, (i , P) ⊢< i > p_succ : P <[ (succ (var 1)) .: (shift >> (shift >> var)) ])
    (t_Wt : Γ ⊢< ty 0 > t : Nat)
    (lvl_eq : l = i)
    (conv_ty : Γ ⊢< Ax i > T ≡ P <[ t.. ] : Sort i)
    : type_inv_data Γ l (rec i P p_zero p_succ t) T
  | type_inv_eq Γ l i A a b T
    (flag : with_strongJ_or_obseq)
    (A_Wt : Γ ⊢< Ax i > A : Sort i)
    (a_Wt : Γ ⊢< i > a : A)
    (b_Wt : Γ ⊢< i > b : A)
    (lvl_eq : l = Ax prop)
    (conv_ty : Γ ⊢< Ax (Ax prop) > T ≡ Sort prop : Sort (Ax prop))
    : type_inv_data Γ l (Eq i A a b) T
  | type_inv_J Γ l l' i A a P p b e T
    (flag : with_strongJ)
    (A_Wt : Γ ⊢< Ax l' > A : Sort l')
    (a_Wt : Γ ⊢< l' > a : A)
    (P_Wt : Γ ,, (l' , A) ⊢< Ax i > P : Sort i)
    (p_Wt : Γ ⊢< i > p : P <[a..])
    (b_Wt : Γ ⊢< l' > b : A)
    (e_Wt : Γ ⊢< prop > e : Eq l' A a b)
    (lvl_eq : l = i)
    (conv_ty : Γ ⊢< Ax i > T ≡ P <[b..] : Sort i)
    : type_inv_data Γ l (J l' i A a P p b e) T
  | inv_data_eqrefl Γ l' A a l T
    (flag : with_strongJ_or_obseq)
    (A_Wt : Γ ⊢< Ax l' > A : Sort l')
    (a_Wt : Γ ⊢< l' > a : A)
    (lvl_eq : l = prop)
    (conv_ty :
       Γ ⊢< Ax prop > T ≡ Eq l' A a a : Sort prop)
    : type_inv_data Γ l (eqrefl l' A a) T
  | type_inv_Lift Γ l l' A T
    (A_Wt : Γ ⊢< Ax l' > A : Sort l')
    (lvl_eq : l = Ax (Ax l'))
    (conv_ty : Γ ⊢< Ax (Ax (Ax l')) > T ≡ Sort (Ax l') : Sort (Ax (Ax l')))
    : type_inv_data Γ l (Lift l' A) T
  | type_inv_lift Γ l l' A a T
    (A_Wt : Γ ⊢< Ax l' > A : Sort l')
    (a_Wt : Γ ⊢< l' > a : A)
    (lvl_eq : l = Ax l')
    (conv_ty : Γ ⊢< Ax (Ax l') > T ≡ Lift l' A : Sort (Ax l'))
    : type_inv_data Γ l (lift l' A a) T
  | type_inv_lower Γ l l' A a T
    (A_Wt : Γ ⊢< Ax l' > A : Sort l')
    (a_Wt : Γ ⊢< Ax l' > a : Lift l' A)
    (lvl_eq : l = l')
    (conv_ty : Γ ⊢< Ax l' > T ≡ A : Sort l')
    : type_inv_data Γ l (lower l' A a) T

  | inv_data_cast Γ i A B e a l T
    (flag : with_obseq)
    (A_Wt : Γ ⊢< Ax i > A : Sort i)
    (B_Wt : Γ ⊢< Ax i > B : Sort i)
    (e_Wt : Γ ⊢< prop > e : Eq (Ax i) (Sort i) A B)
    (a_Wt : Γ ⊢< i > a : A)
    (lvl_eq : l = i)
    (conv_ty :
       Γ ⊢< Ax i > T ≡ B : Sort i)
    : type_inv_data Γ l (cast i A B e a) T

  | inv_data_injpi1 Γ i n A1 A2 B1 B2 e l T
    (flag : with_obseq)
    (A1_Wt : Γ ⊢< Ax i > A1 : Sort i)
    (B1_Wt : Γ ,, (i, A1) ⊢< Ax (ty n) > B1 : Sort (ty n))
    (A2_Wt : Γ ⊢< Ax i > A2 : Sort i)
    (B2_Wt : Γ ,, (i, A2) ⊢< Ax (ty n) > B2 : Sort (ty n))
    (e_Wt :
       Γ ⊢< prop >
         e : Eq (Ax (Ru i (ty n))) (Sort (Ru i (ty n)))
             (Pi i (ty n) A1 B1) (Pi i (ty n) A2 B2))
    (lvl_eq : l = prop)
    (conv_ty :
       Γ ⊢< Ax prop > T ≡ Eq (Ax i) (Sort i) A2 A1 : Sort prop)
    : type_inv_data Γ l (injpi1 i (ty n) A1 A2 B1 B2 e) T

  | inv_data_injpi2 Γ i n A1 A2 B1 B2 e a2 l T
    (flag : with_obseq)
    (A1_Wt : Γ ⊢< Ax i > A1 : Sort i)
    (B1_Wt : Γ ,, (i, A1) ⊢< Ax (ty n) > B1 : Sort (ty n))
    (A2_Wt : Γ ⊢< Ax i > A2 : Sort i)
    (B2_Wt : Γ ,, (i, A2) ⊢< Ax (ty n) > B2 : Sort (ty n))
    (e_Wt :
       Γ ⊢< prop >
         e : Eq (Ax (Ru i (ty n))) (Sort (Ru i (ty n)))
             (Pi i (ty n) A1 B1) (Pi i (ty n) A2 B2))
    (a2_Wt : Γ ⊢< i > a2 : A2)
    (a1 := cast i A2 A1 (injpi1 i (ty n) A1 A2 B1 B2 e) a2)
    (lvl_eq : l = prop)
    (conv_ty :
       Γ ⊢< Ax prop > T ≡
         Eq (Ax (ty n)) (Sort (ty n))
           (B1<[ a1 ..]) (B2<[a2..]) : Sort prop)
    : type_inv_data Γ l (injpi2 i (ty n) A1 A2 B1 B2 e a2) T

  | inv_data_sum Γ i j A B l T :
    Γ ⊢< Ax (ty i) > A : Sort (ty i) →
    Γ ⊢< Ax (ty j) > B : Sort (ty j) →
    Γ ⊢< Ax (Ax (ty (max i j))) > T ≡ Sort (ty (max i j)) : Sort (Ax (ty (max i j))) →
    forall (lvl_eq :l = Ax (ty (max i j))),
    type_inv_data Γ l (tysum (ty i) (ty j) A B) T

  | inv_data_inl Γ i j A B a l T :
    Γ ⊢< Ax (ty i) > A : Sort (ty i) →
    Γ ⊢< Ax (ty j) > B : Sort (ty j) →
    Γ ⊢< ty i > a : A →
    Γ ⊢< Ax (ty (max i j)) > T ≡ tysum (ty i) (ty j) A B : Sort (ty (max i j)) →
    forall (lvl_eq :l = ty (max i j)),
    type_inv_data Γ l (inl (ty i) (ty j) A B a) T

  | inv_data_inr Γ i j A B b l T :
    Γ ⊢< Ax (ty i) > A : Sort (ty i) →
    Γ ⊢< Ax (ty j) > B : Sort (ty j) →
    Γ ⊢< ty j > b : B →
    Γ ⊢< Ax (ty (max i j)) > T ≡ tysum (ty i) (ty j) A B : Sort (ty (max i j)) →
    forall (lvl_eq :l = ty (max i j)),
    type_inv_data Γ l (inr (ty i) (ty j) A B b) T

  | inv_data_sum_case Γ i j l A B P pl pr t k T :
    Γ ⊢< Ax (ty i) > A : Sort (ty i) →
    Γ ⊢< Ax (ty j) > B : Sort (ty j) →
    Γ ,, (ty (max i j), tysum (ty i) (ty j) A B) ⊢< Ax l > P : Sort l →
    Γ ,, (ty i, A) ⊢< l > pl : P <[ (inl (ty i) (ty j) (S ⋅ A) (S ⋅ B) (var 0)) .: S >> var ] →
    Γ ,, (ty j, B) ⊢< l > pr : P <[ (inr (ty i) (ty j) (S ⋅ A) (S ⋅ B) (var 0)) .: S >> var ] →
    Γ ⊢< ty (max i j) > t : tysum (ty i) (ty j) A B →
    Γ ⊢< Ax l > T ≡ P <[ t .. ] : Sort l →
    k = l →
    type_inv_data Γ k (sum_case (ty i) (ty j) l A B P pl pr t) T.

Derive Signature for type_inv_data.

Lemma type_inv Γ l t T :
  Γ ⊢< l > t : T ->
  type_inv_data Γ l t T.
Proof.
  intros.
  apply validity_ty_ty in H as T_Wt.
  induction H. 1-26:econstructor; eauto using conv_refl.
  eapply validity_conv_left in H0 as AWt.
  eapply IHtyping in AWt as IH.
  depelim IH; econstructor; subst; eauto using conv_sym, conv_trans.
Qed.


(* Type uniqueness *)

Theorem var_unique Γ l x A l' A' :
  Γ ∋< l > x : A ->
  Γ ∋< l' > x : A' ->
  l = l' /\ A = A'.
Proof.
  generalize Γ l l' A A'. clear Γ l l' A A'.
  induction x; intros.
  - dependent destruction H. dependent destruction H0. split; eauto.
  - dependent destruction H. dependent destruction H0.
    eapply IHx in H as (HA & HB); eauto. subst. split; eauto.
Qed.

Ltac ty_inj_tac :=
  repeat match goal with
  | H : ty ?n = ty ?m |- _ => eapply ty_inj in H
  end.

Theorem type_sort_unique Γ l l' t A B :
  Γ ⊢< l > t : A ->
  Γ ⊢< l' > t : B ->
  Γ ⊢< Ax l > A ≡ B : Sort l /\ l = l'.
Proof.
  intros.
  induction H.
  2-26:eapply type_inv in H0; dependent destruction H0; ty_inj_tac; subst; eauto 15 using conv_sym.
  - eapply type_inv in H0. dependent destruction H0.
    eapply var_unique in H1 as (HA & HB); eauto. subst. eauto using conv_sym.
  - eapply IHtyping in H0 as (HA & HB). subst. eauto using conv_sym, conv_trans.
Qed.

Corollary type_unique Γ l l' t A B :
  Γ ⊢< l > t : A ->
  Γ ⊢< l' > t : B ->
  Γ ⊢< Ax l > A ≡ B : Sort l.
Proof.
  intros. eapply type_sort_unique in H as (HA & HB); eauto. subst.
  eauto using conv_sym.
Qed.

Corollary sort_unique Γ l l' t A B :
  Γ ⊢< l > t : A ->
  Γ ⊢< l' > t : B ->
  l = l'.
Proof.
  intros. eapply type_sort_unique in H as (HA & HB); eauto.
Qed.

(* Linerized versions of computation rules *)

Lemma conv_J_refl' Γ l i A a b P p e :
  with_strongJ ->
  Γ ⊢< Ax l > A : Sort l ->
  Γ ⊢< l > a ≡ b : A ->
  Γ ,, (l , A) ⊢< Ax i > P : Sort i ->
  Γ ⊢< i > p : P <[a..] ->
  Γ ⊢< prop > e : Eq l A a b ->
  Γ ⊢< i > J l i A a P p b e ≡ p : P <[b..].
Proof.
  intros.
  eapply conv_trans. 1:eapply conv_J; eauto using conv_refl, validity_conv_right. 
  eapply conv_J_refl; eauto using validity_conv_right.
  1:eapply type_conv; eauto using validity_conv_right.
  1:eapply subst_conv; eauto using substs_one, conv_refl, validity_ty_ctx.
  1:eapply type_conv; eauto 7 using conv_Eq, validity_conv_right, conv_refl.
Qed.

Lemma conv_beta' Γ i j A A' B B' t u :
      Γ ⊢< Ax i > A ≡ A' : Sort i →
      Γ ,, (i , A) ⊢< Ax j > B ≡ B' : Sort j →
      Γ ,, (i , A') ⊢< j > t : B' →
      Γ ⊢< i > u : A →
      Γ ⊢< j > app i j A B (lam i j A' B' t) u ≡ t <[ u .. ] : B <[ u .. ].
Proof.
  intros.
  eapply conv_trans.
  1:eapply conv_app. 4:eapply conv_conv. 4:eapply conv_lam.
  all: eauto using conv_refl, validity_conv_left, validity_conv_right, validity_ty_ty.
  1:eapply conv_pi; eauto using validity_conv_right, conv_sym, conv_ty_in_ctx_conv.
  eapply conv_conv. 1:eapply conv_beta.
  all:eauto using validity_ty_ty, validity_conv_right, type_conv.
  eapply subst_conv; eauto using substs_one, conv_refl, validity_ty_ctx, conv_sym.
Qed.

Lemma conv_pi1pair' Γ n m A B A' B' a b :
      Γ ⊢< Ax (ty n) > A ≡ A' : Sort (ty n) →
      Γ ,, (ty n , A) ⊢< Ax (ty m) > B ≡ B' : Sort (ty m) →
      Γ ⊢< ty n > a : A →
      Γ ⊢< ty m > b : B <[a..] →
      Γ ⊢< ty n > pi1 (ty n) (ty m) A B (pair (ty n) (ty m) A' B' a b) ≡ a : A.
Proof.
  intros.
  eapply conv_trans.
  - eapply conv_pi1. 2,3:eapply conv_refl.  1-3:eauto using validity_conv_left.
    eapply conv_conv.
    + econstructor; eauto using conv_sym, validity_conv_left, conv_ty_in_ctx_conv.
      all:eapply conv_refl, type_conv; eauto.
      eapply subst_conv; eauto using validity_ty_ctx, substs_one, conv_refl.
    + econstructor; eauto using conv_sym, validity_conv_left, conv_ty_in_ctx_conv.
  - eapply conv_pi1pair; eauto using validity_conv_left.
Qed.

Lemma conv_pi2pair' Γ n m A B A' B' a b :
      Γ ⊢< Ax (ty n) > A ≡ A' : Sort (ty n) →
      Γ ,, (ty n , A) ⊢< Ax (ty m) > B ≡ B' : Sort (ty m) →
      Γ ⊢< ty n > a : A →
      Γ ⊢< ty m > b : B <[a..] →
      Γ ⊢< ty m > pi2 (ty n) (ty m) A B (pair (ty n) (ty m) A' B' a b) ≡ b : B<[a..].
Proof.
  intros.
  eapply conv_trans.
  - eapply conv_conv.
    + eapply conv_pi2. 2,3:eapply conv_refl.  1-3:eauto using validity_conv_left.
      eapply conv_conv.
      * econstructor; eauto using conv_sym, validity_conv_left, conv_ty_in_ctx_conv.
        all:eapply conv_refl, type_conv; eauto.
        eapply subst_conv; eauto using validity_ty_ctx, substs_one, conv_refl.
      * econstructor; eauto using conv_sym, validity_conv_left, conv_ty_in_ctx_conv.
    + eapply subst_conv; eauto using validity_conv_left, conv_refl, validity_ty_ctx.
      eapply substs_one. eapply conv_pi1pair'; eauto.
  - eapply conv_pi2pair; eauto using validity_conv_left.
Qed.

Lemma conv_lower_lift' Γ n A A' a :
      Γ ⊢< Ax (ty n) > A ≡ A' : Sort (ty n) ->
      Γ ⊢< ty n > a : A ->
      Γ ⊢< ty n > lower (ty n) A (lift (ty n) A' a) ≡ a : A.
Proof.
  intros.
  eapply conv_trans.
  + eapply conv_lower. 1:eapply conv_refl; eauto using validity_conv_left.
    eapply conv_conv. 1:eapply conv_lift; eauto using conv_sym, conv_conv, conv_refl.
    eapply conv_Lift; eauto using conv_sym.
  + eapply conv_lower_lift; eauto using validity_conv_left, validity_conv_right.
Qed.

Lemma conv_lift_lower' Γ n A A' a :
      Γ ⊢< Ax (ty n) > A ≡ A' : Sort (ty n) ->
      Γ ⊢< Ax (ty n) > a : Lift (ty n) A ->
      Γ ⊢< Ax (ty n) > lift (ty n) A (lower (ty n) A' a) ≡ a : Lift (ty n) A.
Proof.
  intros. eapply conv_trans.
  + eapply conv_lift. 1:eapply conv_refl; eauto using validity_conv_left.
    eapply conv_conv. 1:eapply conv_lower; eauto using conv_sym, conv_conv, conv_Lift, conv_refl.
    eauto using conv_sym.
  + eapply conv_lift_lower; eauto using validity_conv_left, validity_conv_right.
Qed.

Lemma conv_injpi1' Γ i n A1 A1' A2 A2' B1 B1' B2 B2' e e' :
    with_obseq ->
    Γ ⊢< Ax i > A1 ≡ A1' : Sort i ->
    Γ ,, (i, A1) ⊢< Ax (ty n) > B1 ≡ B1' : Sort (ty n) ->
    Γ ⊢< Ax i > A2 ≡ A2' : Sort i ->
    Γ ,, (i, A2) ⊢< Ax (ty n) > B2 ≡ B2' : Sort (ty n) ->
    Γ ⊢< prop > e ≡ e' : Eq (Ax (Ru i (ty n))) (Sort (Ru i (ty n))) (Pi i (ty n) A1 B1) (Pi i (ty n) A2 B2) ->
    Γ ⊢< prop > injpi1 i (ty n) A1 A2 B1 B2 e ≡ injpi1 i (ty n) A1' A2' B1' B2' e' : Eq (Ax i) (Sort i) A2 A1.
Proof.
  intros; econstructor; eauto using validity_conv_left.
Qed.

Lemma conv_injpi2' Γ i n A1 A1' A2 A2' B1 B1' B2 B2' e e' a2 a2' :
    with_obseq ->
    Γ ⊢< Ax i > A1 ≡ A1' : Sort i ->
    Γ ,, (i, A1) ⊢< Ax (ty n) > B1 ≡ B1' : Sort (ty n) ->
    Γ ⊢< Ax i > A2 ≡ A2' : Sort i ->
    Γ ,, (i, A2) ⊢< Ax (ty n) > B2 ≡ B2' : Sort (ty n) ->
    Γ ⊢< prop > e ≡ e' : Eq (Ax (Ru i (ty n))) (Sort (Ru i (ty n))) (Pi i (ty n) A1 B1) (Pi i (ty n) A2 B2) ->
    Γ ⊢< i > a2 ≡ a2' : A2 ->
    let a1 := cast i A2 A1 (injpi1 i (ty n) A1 A2 B1 B2 e) a2 in
    Γ ⊢< prop > injpi2 i (ty n) A1 A2 B1 B2 e a2 ≡ injpi2 i (ty n) A1' A2' B1' B2' e' a2' : Eq (Ax (ty n)) (Sort (ty n)) (B1<[a1..]) (B2 <[a2..]).
Proof.
  intros; econstructor; eauto using validity_conv_left.
Qed.

Lemma conv_sum_case_inl' Γ i j l A A' B B' P pl pr a :
  Γ ⊢< Ax (ty i) > A ≡ A' : Sort (ty i) →
  Γ ⊢< Ax (ty j) > B ≡ B' : Sort (ty j) →
  Γ ,, (ty (max i j), tysum (ty i) (ty j) A B) ⊢< Ax l > P : Sort l →
  Γ ,, (ty i, A) ⊢< l > pl : P <[ (inl (ty i) (ty j) (S ⋅ A) (S ⋅ B) (var 0)) .: S >> var ] →
  Γ ,, (ty j, B) ⊢< l > pr : P <[ (inr (ty i) (ty j) (S ⋅ A) (S ⋅ B) (var 0)) .: S >> var ] →
  Γ ⊢< ty i > a : A →
  Γ ⊢< l > sum_case (ty i) (ty j) l A B P pl pr (inl (ty i) (ty j) A' B' a) ≡ pl <[ a .. ] : P <[ (inl (ty i) (ty j) A B a) .. ].
Proof.
  intros. eapply conv_trans.
  - eapply conv_sym. eapply conv_sum_case.
    all: eauto using validity_conv_left, conv_refl.
    econstructor. all: eauto using validity_conv_left, conv_refl.
  - eapply conv_sum_case_inl. all: eauto using validity_conv_left.
Qed.

Lemma conv_sum_case_inr' Γ i j l A A' B B' P pl pr b :
  Γ ⊢< Ax (ty i) > A ≡ A' : Sort (ty i) →
  Γ ⊢< Ax (ty j) > B ≡ B' : Sort (ty j) →
  Γ ,, (ty (max i j), tysum (ty i) (ty j) A B) ⊢< Ax l > P : Sort l →
  Γ ,, (ty i, A) ⊢< l > pl : P <[ (inl (ty i) (ty j) (S ⋅ A) (S ⋅ B) (var 0)) .: S >> var ] →
  Γ ,, (ty j, B) ⊢< l > pr : P <[ (inr (ty i) (ty j) (S ⋅ A) (S ⋅ B) (var 0)) .: S >> var ] →
  Γ ⊢< ty j > b : B →
  Γ ⊢< l > sum_case (ty i) (ty j) l A B P pl pr (inr (ty i) (ty j) A' B' b) ≡ pr <[ b .. ] : P <[ (inr (ty i) (ty j) A B b) .. ].
Proof.
  intros. eapply conv_trans.
  - eapply conv_sym. eapply conv_sum_case.
    all: eauto using validity_conv_left, conv_refl.
    econstructor. all: eauto using validity_conv_left, conv_refl.
  - eapply conv_sum_case_inr. all: eauto using validity_conv_left.
Qed.
