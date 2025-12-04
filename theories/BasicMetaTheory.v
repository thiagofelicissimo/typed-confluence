
From Stdlib Require Import Utf8 List Arith Bool Lia.
From TypedConfluence
Require Import core unscoped Util Ast SubstNotations RAsimpl AST_rasimpl.
From TypedConfluence Require Import BasicAST Contexts Typing.
From Stdlib Require Import Setoid Morphisms Relation_Definitions.
Require Import Equations.Prop.DepElim.
From Equations Require Import Equations.

Import ListNotations.
Import CombineNotations.

Open Scope subst_scope.

Set Default Goal Selector "!".

Derive Signature for varty.
Derive Signature for ctx_typing.
Derive Signature for typing.

Lemma Ax_inj l l' : Ax l = Ax l' -> l = l'.
Proof.
  intro H. destruct l; destruct l'; inversion H; auto.
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
  2,3,4,6,7,8,10,12,14,15,16,18,19,20,22,24,25,30,31:
    solve [ intros ; try econstructor ; eauto using WellRen_up, ctx_cons ].

  2,3,4,6,7,8:
    solve [intros; cbn in *; (eapply meta_conv_conv + eapply meta_conv) ;
            [ (econstructor ; try solve [ (eapply meta_conv_conv + eapply meta_conv) ;
              [ eauto 11 using WellRen_up, WellRen_meta, ctx_typing, typing, ctx_cons
              | rasimpl ; reflexivity]])
            | rasimpl; reflexivity]].

  3-6: solve [ intros; cbn; eapply meta_conv_conv;
              [ eapply meta_rhs_conv;
                [ ((eapply conv_beta + eapply conv_rec_zero + eapply conv_rec_succ + eapply conv_J_refl) ;
                  eauto using ctx_typing, typing, WellRen_up; try (eapply meta_conv;
                  [ eauto 12 using ctx_typing, typing, WellRen_up
                  | rasimpl; reflexivity]))
                | ssimpl; reflexivity]
              | ssimpl; reflexivity] ].

  all: solve [intro;cbn; econstructor; eauto using varty_ren].
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

  2,3,4,6,7,8,10,12,14,15,16,18,19,20,22,24,25,30,31:
    solve [ try econstructor ; eauto 8 using WellSubst_up, ctx_cons ].

  all: try assert (Δ,, (ty 0, Nat) ⊢< Ax l > P <[ up_term_term σ] : Sort l)
      by eauto 6 using ctx_typing, typing, WellSubst_meta, WellSubst_up.

  2,3,4,6,7,8:solve [cbn in *; (eapply meta_conv_conv + eapply meta_conv) ;
            [ (econstructor ; try solve [ (eapply meta_conv_conv + eapply meta_conv) ;
              [ eauto 11 using WellRen_up, WellSubst_up, WellSubst_meta, ctx_typing, typing, ctx_cons
              | rasimpl ; reflexivity]])
            | rasimpl; reflexivity]].

  3-6: solve [ intros; cbn; eapply meta_conv_conv;
                [ eapply meta_rhs_conv;
                  [ ((eapply conv_beta + eapply conv_rec_zero + eapply conv_rec_succ + eapply conv_J_refl) ;
                    eauto using ctx_typing, typing, WellRen_up, WellSubst_up, WellSubst_meta; try (eapply meta_conv;
                    [ eauto 12 using ctx_typing, typing, WellRen_up, WellSubst_up, WellSubst_meta
                    | rasimpl; reflexivity]))
                  | ssimpl; reflexivity]
                | ssimpl; reflexivity] ].


  - cbn. eapply varty_subst. all: eassumption.
  - cbn. apply conv_refl.
    eapply varty_subst. all: eassumption.
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


Lemma conv_substs Γ Δ σ σ' t l A :
  ⊢ Δ ->
  Δ ⊢s σ ≡ σ' : Γ →
  Δ ⊢s σ : Γ →
  Γ ⊢< l > t : A →
  Δ ⊢< l > t <[ σ ] ≡ t <[ σ' ] : A <[ σ ].
Proof.
  intros h hs hst ht.
  induction ht in Δ, σ, σ', h, hs, hst |- *; cbn.
  2-4,6-8,10: solve [ econstructor ; eauto 10 using conv_substs_up, WellSubst_up, ctx_typing, subst_ty ].
  - eauto using varty_conv_substs.
  - eapply meta_conv_conv.
    + econstructor. all: eauto 9 using conv_substs_up, WellSubst_up, ctx_typing, subst_ty.
    + rasimpl; reflexivity.
  - assert (Δ,, (ty 0, Nat) ⊢< Ax l > P <[ up_term_term σ] : Sort l)
      by (eapply typing_conversion_subst in ht1; eauto using typing, ctx_typing, WellSubst_up).
    eapply meta_conv_conv.
    + econstructor.
          all : try solve [ (eapply meta_conv_conv + eapply meta_conv) ; [
        eauto 12 using ctx_typing, typing, WellSubst_up, conv_substs_up, subst_conv_meta_conv_ctx, subst_meta_conv_ctx | rasimpl ; reflexivity]].
    + rasimpl; reflexivity.
  - eapply meta_conv_conv.
    + econstructor.
          all : try solve [ (eapply meta_conv_conv + eapply meta_conv) ; [
        eauto 8 using subst_ty, ctx_typing, typing, WellSubst_up, conv_substs_up, subst_conv_meta_conv_ctx, subst_meta_conv_ctx | rasimpl ; reflexivity]].
    + rasimpl; reflexivity.
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
  all: try solve [ intros ; econstructor ; eauto using validity_ty_ctx, validity_conv_ctx].
  all: try solve [
    intros ; try econstructor ; try econstructor ; intuition eauto using validity_ty_ctx, validity_conv_ctx
  ].

  1,2,4,5,6,11,13,14,17,18: solve [ intuition eauto using subst_ty, subst_one, validity_ty_ctx, typing, validity_ty_ctx, subst_one, valid_varty].


  (* TODO: investigate if the remaining cases can be further automated *)

  - intros. eapply meta_lvl; eauto using typing.
  - intros Γ i j A B **.
    split ; econstructor. all: intuition eauto.
    eapply pre_conv_in_ctx_ty. all: eauto using ctx_typing, validity_ty_ctx, ctx_conv_refl, conv_ccons, conv_sym.
  - intros Γ i j A B **.
    split.
    + econstructor. all: intuition eauto.
    + econstructor.
      * {
        econstructor. 1: intuition eauto.
        all: intuition eauto 9 using pre_conv_in_ctx_ty, ctx_conv_refl, conv_ccons, conv_sym, ctx_typing, validity_ty_ctx.
        eapply pre_conv_in_ctx_ty.
        - eapply type_conv. all: intuition eauto.
        - econstructor; eauto using validity_ty_ctx.
        - econstructor; eauto using conv_sym, ctx_conv_refl, validity_ty_ctx.
      }
      * apply conv_sym. constructor.
        all: intuition eauto.
  - intros Γ i j A B **.
    split.
    + econstructor. all: intuition eauto.
    + eapply type_conv.
      * {
        econstructor. 1: intuition eauto.
        all: intuition eauto 8 using type_conv, pre_conv_in_ctx_ty, ctx_conv_refl, conv_ccons, conv_sym, ctx_typing, validity_ty_ctx.
        eapply type_conv. 1: intuition eauto.
        constructor. all: intuition eauto.
      }
      * {
        apply conv_sym. eapply conv_trans.
        - eapply meta_conv_conv.
          + eapply typing_conversion_subst.
            all: intuition eauto using subst_one, validity_ty_ctx.
          + reflexivity.
        - eapply meta_conv_conv.
          { eapply conv_substs.
            - eauto using validity_ty_ctx.
            - eapply substs_one. eauto.
            - eapply subst_one. intuition eauto.
            - intuition eauto.
          }
          reflexivity.
      }
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
  - intros. destruct H0, H1, H2, H3, H4, H5. split.
    + eapply type_J; eauto.
    + eapply type_conv. 1:eapply type_J; eauto using type_conv, conv_Eq.
      1:eapply pre_conv_in_ctx_ty; eauto using ctx_typing, validity_ty_ctx, conv_ccons, ctx_conv_refl, conv_sym.
      1:eapply type_conv; eauto.
      1,2: eapply pre_subst_conv; eauto using subst_one, validity_ty_ctx, substs_one, conv_sym.
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
  - intros. split.
    + eapply type_J; eauto.
    + eauto.
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
  intros t_eq_u A_eq_A'.
  eapply conv_in_ctx_ty; eauto.
  apply conv_ccons; eauto using ctx_conv_refl, validity_ty_ctx, validity_conv_left.
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

Derive NoConfusion for term.
Derive NoConfusion for level.


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
    (A_Wt : Γ ⊢< Ax i > A : Sort i)
    (a_Wt : Γ ⊢< i > a : A)
    (b_Wt : Γ ⊢< i > b : A)
    (lvl_eq : l = Ax prop)
    (conv_ty : Γ ⊢< Ax (Ax prop) > T ≡ Sort prop : Sort (Ax prop))
    : type_inv_data Γ l (Eq i A a b) T
  | type_inv_J Γ l l' i A a P p b e T
    (A_Wt : Γ ⊢< Ax l' > A : Sort l')
    (a_Wt : Γ ⊢< l' > a : A)
    (P_Wt : Γ ,, (l' , A) ⊢< Ax i > P : Sort i)
    (p_Wt : Γ ⊢< i > p : P <[a..])
    (b_Wt : Γ ⊢< l' > b : A)
    (e_Wt : Γ ⊢< prop > e : Eq l' A a b)
    (lvl_eq : l = i)
    (conv_ty : Γ ⊢< Ax i > T ≡ P <[b..] : Sort i)
    : type_inv_data Γ l (J l' i A a P p b e) T.

Derive Signature for type_inv_data.

Lemma type_inv Γ l t T :
  Γ ⊢< l > t : T ->
  type_inv_data Γ l t T.
Proof.
  intros.
  apply validity_ty_ty in H as T_Wt.
  induction H. 1-11:econstructor; eauto using conv_refl.
  eapply validity_conv_left in H0 as AWt.
  eapply IHtyping in AWt as IH.
  depelim IH; econstructor; subst; eauto using conv_sym, conv_trans.
Qed.


Theorem var_unicity Γ l x A l' A' :
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


Theorem type_sort_unicity Γ l l' t A B :
  Γ ⊢< l > t : A ->
  Γ ⊢< l' > t : B ->
  Γ ⊢< Ax l > A ≡ B : Sort l /\ l = l'.
Proof.
  intros.
  induction H.
  2-11:eapply type_inv in H0; dependent destruction H0; subst; eauto 13 using conv_sym.
  - eapply type_inv in H0. dependent destruction H0.
    eapply var_unicity in H1 as (HA & HB); eauto. subst. eauto using conv_sym.
  - eapply IHtyping in H0 as (HA & HB). subst. eauto using conv_sym, conv_trans.
Qed.

Corollary type_unicity Γ l l' t A B :
  Γ ⊢< l > t : A ->
  Γ ⊢< l' > t : B ->
  Γ ⊢< Ax l > A ≡ B : Sort l.
Proof.
  intros. eapply type_sort_unicity in H as (HA & HB); eauto. subst.
  eauto using conv_sym.
Qed.

Corollary sort_unicity Γ l l' t A B :
  Γ ⊢< l > t : A ->
  Γ ⊢< l' > t : B ->
  l = l'.
Proof.
  intros. eapply type_sort_unicity in H as (HA & HB); eauto.
Qed.


Lemma conv_J_refl' Γ l i A a b P p e :
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
  1:eapply type_conv; eauto using conv_Eq, validity_conv_right, conv_refl.
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
