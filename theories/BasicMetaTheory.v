
From Stdlib Require Import Utf8 List Arith Bool Lia.
From TypedConfluence
Require Import core unscoped Ast SubstNotations RAsimpl AST_rasimpl.
From TypedConfluence Require Import Util BasicAST Weakenings Contexts Typing. (*  Env Inst. *)
From Stdlib Require Import Setoid Morphisms Relation_Definitions.
Require Import Stdlib.Program.Equality.

Import ListNotations.
Import CombineNotations.

Open Scope subst_scope.

Set Default Goal Selector "!".

Lemma Ax_inj l l' : Ax l = Ax l' -> l = l'.
Proof.
  intro H. destruct l; destruct l'; inversion H; auto.
Qed.

(* basic inversion lemmas *)


Lemma type_inv_var Γ l x T :
  Γ ⊢< l > var x : T →
  ∃ A, Γ ∋< l > x : A.
Proof.
  intro H.
  dependent induction H; eauto.
Qed.

Lemma type_inv_pi Γ l' i j A B T:
  Γ ⊢< l' > Pi i j A B : T ->
  Γ ⊢< Ax i > A : Sort i /\ Γ ,, (i, A) ⊢< Ax j > B : Sort j.
Proof.
  intro H.
  dependent induction H; eauto.
Qed.

Lemma type_inv_lam Γ i j A B t T l :
      Γ ⊢< l > lam i j A B t : T ->
      Γ ⊢< Ax i > A : Sort i /\
      Γ ,, (i , A) ⊢< Ax j > B : Sort j /\
      Γ ,, (i , A) ⊢< j > t : B.
Proof.
  intro H.
  dependent induction H; eauto.
Qed.

Lemma type_inv_app Γ i j A B t u l T :
      Γ ⊢< l > app i j A B  t u : T ->
      Γ ⊢< Ax i > A : Sort i /\
      Γ ,, (i , A) ⊢< Ax j > B : Sort j /\
      Γ ⊢< Ru i j > t : Pi i j A B /\
      Γ ⊢< i > u : A.
Proof.
  intro H.
  dependent induction H; eauto.
Qed.

Lemma type_inv_succ Γ t T l :
      Γ ⊢< l > succ t : T ->
      Γ ⊢< ty 0 > t : Nat.
Proof.
  intro H.
  dependent induction H; eauto.
Qed.

Lemma type_inv_rec Γ l' l P p_zero p_succ t T :
  Γ ⊢< l' > rec l P p_zero p_succ t : T ->
  Γ ,, (ty 0 , Nat) ⊢< Ax l > P : Sort l /\
  Γ ⊢< l > p_zero : P <[ zero .. ] /\
  Γ ,, (ty 0 , Nat) ,, (l , P) ⊢< l > p_succ : P <[ (succ (var 1)) .: (shift >> (shift >> var)) ] /\
  Γ ⊢< ty 0 > t : Nat.
Proof.
  intro H.
  dependent induction H; eauto.
Qed.

Lemma type_inv_box Γ T l :
      Γ ⊢< l > box : T ->
      False.
Proof.
  intro H.
  dependent induction H; eauto.
Qed.


(*
  To prove the following properties, we can try to follow the same order as in
  Harper & Pfenning's "On equivalence and canonical forms in the lf type theory".
  In any case, there is no doubt that they can be proven.
*)

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
  all: try solve [ intros ; try econstructor ; eauto using WellRen_up, ctx_cons ].
  all: try solve [
    intros ; cbn in * ; (eapply meta_conv + eapply meta_conv_conv) ; [
      econstructor ; eauto using WellRen_up, ctx_cons
    | rasimpl ; reflexivity
    ]
  ].
  (* The proof is not very satisfactory, I expect there is some automation
    hidden below this but I'm not sure what.
  *)
  - intros.
    cbn. constructor. 1: auto.
    eapply varty_ren. all: eassumption.
  - intros ?? P ???? ihP ? ihz ? ihs ? iht Δ ρ ? hr.
    assert (⊢ Δ ,, (ty 0, Nat)).
    { constructor. 1: auto.
      constructor. assumption.
    }
    assert (Δ ,, (ty 0, Nat) ⊢< Ax l > up_ren ρ ⋅ P : Sort l).
    { eapply ihP. 1: auto.
      eapply WellRen_meta. 1: eapply WellRen_up. all: eauto.
      reflexivity.
    }
    cbn in *. eapply meta_conv.
    + econstructor. all: eauto using WellRen_up, WellRen_meta.
      * eapply meta_conv. all: eauto using WellRen_up, WellRen_meta.
        rasimpl. reflexivity.
      * {
        eapply meta_conv.
        - eapply ihs. 1:{ constructor. all: eauto. }
          eapply WellRen_meta. 1: repeat eapply WellRen_up.
          all: eauto.
          reflexivity.
        - rasimpl. reflexivity.
      }
    + rasimpl. reflexivity.
  - intros.
    cbn. constructor. 1: auto.
    eapply varty_ren. all: eassumption.
  - intros. cbn in *. eapply meta_conv_conv.
    + econstructor. all: eauto using WellRen_up, ctx_typing, typing.
      * eapply meta_conv_conv. 1:eapply H1. all:rasimpl;eauto.
      * eapply meta_conv_conv. 1:eapply H2.
        all: rasimpl; eauto 9 using ctx_typing, typing, WellRen_up.
    + rasimpl; eauto.
  - intros. cbn. eapply meta_conv_conv. 
    1: eapply meta_rhs_conv.
    1: eapply conv_beta; eauto using ctx_typing, typing, WellRen_up.
    all:rasimpl; eauto.
  - intros. cbn. eapply meta_conv_conv. 1:eapply meta_rhs_conv.
    1: { eapply conv_rec_zero; eauto using ctx_typing, typing, WellRen_up.
         1: eapply meta_conv.  1: eapply H0. 1-3:rasimpl; eauto.
         eapply meta_conv. 1:eapply H1.  
         1-3:rasimpl; eauto 9 using ctx_typing, typing, WellRen_up. }
    all:rasimpl; eauto.
  - intros. cbn. eapply meta_conv_conv. 1:eapply meta_rhs_conv.
    1: { eapply conv_rec_succ; eauto using ctx_typing, typing, WellRen_up.
         1: eapply meta_conv.  1: eapply H0. 1-3:rasimpl; eauto.
         eapply meta_conv. 1:eapply H1.  
         1-3:rasimpl; eauto 9 using ctx_typing, typing, WellRen_up. }
    all:ssimpl; reflexivity.
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
  apply typing_mutind.
  all: try solve [ intros ; try econstructor ; eauto 8 using WellSubst_up, ctx_typing ].
  all: try solve [
    intros ; cbn in * ; (eapply meta_conv + eapply meta_conv_conv) ; [
      econstructor ; eauto 8 using WellSubst_up, ctx_typing
    | rasimpl ; reflexivity
    ]
  ].


  - intros.
    cbn. eapply varty_subst. all: eassumption.
  - intros ??????? ihP ? ihz ? ihs ? iht ?? wf hs.
    cbn in *. 
    assert (Δ,, (ty 0, Nat) ⊢< Ax l > P <[ up_term_term σ] : Sort l).
    { 
      eapply ihP; eauto using ctx_typing, typing. eapply WellSubst_meta. 1: eapply WellSubst_up. 
      all: eauto. all:eauto using typing.
    }
    eapply meta_conv.
    + econstructor. all: eauto using WellSubst_up, WellSubst_meta.
      * eapply meta_conv. all: eauto using WellSubst_up, WellSubst_meta.
        rasimpl. reflexivity.
      * {
        eapply meta_conv.
        - eapply ihs.
          1:econstructor;  eauto using ctx_typing, typing. 
        eapply WellSubst_meta. 1: repeat eapply WellSubst_up.
          all: eauto.
          1,2: eauto using typing.
          reflexivity.
        - rasimpl. reflexivity.
      }
    + rasimpl. reflexivity.
  - intros.
    cbn. apply conv_refl.
    eapply varty_subst. all: eassumption.
  - intros.
    assert (Δ,, (ty 0, Nat) ⊢< Ax l > P <[ up_term_term σ] : Sort l).
    { 
      eapply H; eauto using ctx_typing, typing. eapply WellSubst_meta. 1: eapply WellSubst_up. 
      all: eauto. all:eauto using typing.
    }
    cbn in *. eapply meta_conv_conv.
    + econstructor. all: eauto using WellSubst_up, WellSubst_meta.
      * eapply H0; eauto using ctx_typing, typing. eapply WellSubst_meta. 1: eapply WellSubst_up. 
        all: eauto using typing. 1:eauto using typing.
        reflexivity.
      * eapply meta_conv_conv. all: eauto using WellSubst_up, WellSubst_meta.
        rasimpl. reflexivity.
      * {
        eapply meta_conv_conv.
        - eapply H2; eauto using ctx_typing, typing.  
          eapply WellSubst_meta. 1: repeat eapply WellSubst_up.
          all: eauto. 1,2:eauto using typing.
          reflexivity.
        - rasimpl. reflexivity.
      }
    + rasimpl. reflexivity.
  - intros.
    cbn. rasimpl. 
    assert (Δ ⊢< Ax i > A <[ σ] : Sort i) by (eapply H; eauto using ctx_typing, typing).
    eapply meta_conv_conv.
    1:{
      eapply meta_rhs_conv.
      1:{
        eapply conv_beta. all: eauto using WellSubst_up, ctx_typing.
      }
      rasimpl. reflexivity.
    }
    rasimpl. reflexivity.
  - intros ?????? ihP ? ihz ? ihs ?? hs wf.
    assert (Δ,, (ty 0, Nat) ⊢< Ax l > P <[ up_term_term σ] : Sort l).
    { 
      eapply ihP; eauto using ctx_typing, typing. eapply WellSubst_meta. 1: eapply WellSubst_up. 
      all: eauto. all:eauto using typing.
    }
    cbn. eapply meta_conv_conv.
    1:{
      eapply conv_rec_zero. 1:eauto.
      - eapply meta_conv. all: eauto using WellSubst_up, WellSubst_meta.
        rasimpl. reflexivity.
      - eapply meta_conv.
        + eapply ihs;eauto using ctx_typing, typing. eapply WellSubst_meta. 1: repeat eapply WellSubst_up.
          all: eauto. all:eauto using typing.
        + rasimpl. reflexivity.
    }
    rasimpl. reflexivity.
  - intros ??????? ihP ? ihz ? ihs ? iht ?? hs wf.
    assert (Δ,, (ty 0, Nat) ⊢< Ax l > P <[ up_term_term σ] : Sort l).
    { 
      eapply ihP; eauto using ctx_typing, typing. eapply WellSubst_meta. 1: eapply WellSubst_up. 
      all: eauto. all:eauto using typing.
    }
    cbn. eapply meta_conv_conv.
    1:{
      eapply meta_rhs_conv.
      1:{
        eapply conv_rec_succ.  all: eauto using WellSubst_up, WellSubst_meta.
        - eapply meta_conv. all: eauto using WellSubst_up, WellSubst_meta.
          rasimpl. reflexivity.
      - eapply meta_conv.
        + eapply ihs;eauto using ctx_typing, typing. eapply WellSubst_meta. 1: repeat eapply WellSubst_up.
          all: eauto. all:eauto using typing.
        + rasimpl. reflexivity.
      }
      rasimpl. reflexivity.
    }
    rasimpl. reflexivity.
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

(* Lemma ctx_conv_sym Γ Δ :
  ⊢ Γ ≡ Δ →
  ⊢ Δ ≡ Γ.
Proof.
  intros h. induction h.
  - constructor.
  - constructor. *)

(* TODO Maybe useless *)
(* Lemma ctx_conv_varty Γ Δ x A l :
  ⊢ Γ ≡ Δ →
  Γ ∋< l > x : A →
  ∃ B, Δ ∋< l > x : B ∧ Γ ⊢< Ax l > A ≡ B : Sort l.
Proof.
  intros hc h.
  induction hc as [| Γ B Δ C i hc ih hbc ] in x, l, A, h |- *.
  - inversion h.
  - inversion h. all: subst.
    + eexists. split.
      * constructor.
      * eapply meta_conv_conv.
        { eapply typing_conversion_ren. all: eauto using WellRen_S. }
        reflexivity.
    + specialize ih with (1 := ltac:(eassumption)).
      destruct ih as (D & hx & he).
      eexists. split.
      * constructor. eassumption.
      * eapply meta_conv_conv.
        { eapply typing_conversion_ren. all: eauto using WellRen_S. }
        reflexivity.
Qed. *)

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


Lemma typing_ctx_conv Γ Δ t l A :
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

Lemma conversion_ctx_conv Γ Δ u v l A :
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

Lemma conv_substs Γ Δ σ σ' t l A :
  ⊢ Δ ->
  Δ ⊢s σ ≡ σ' : Γ →
  Δ ⊢s σ : Γ →
  Γ ⊢< l > t : A →
  Δ ⊢< l > t <[ σ ] ≡ t <[ σ' ] : A <[ σ ].
Proof.
  intros h hs hst ht.
  induction ht in Δ, σ, σ', h, hs, hst |- *.
  3,4,5:assert (Δ ⊢< Ax i > A <[ σ] : Sort i) by (eapply typing_conversion_subst in ht1; eauto).
  all: try solve [ cbn in * ; econstructor ; eauto using conv_substs_up, WellSubst_up, ctx_typing ].
  - cbn. eauto using varty_conv_substs.
  - cbn in *. 
    eapply meta_conv_conv.
    { constructor. all: eauto using conv_substs_up, WellSubst_up, ctx_typing. }
    rasimpl. reflexivity.
  - cbn in *. 
    assert (Δ,, (ty 0, Nat) ⊢< Ax l > P <[ up_term_term σ] : Sort l) 
      by (eapply typing_conversion_subst in ht1; eauto using typing, ctx_typing, WellSubst_up).
    eapply meta_conv_conv.
    { constructor. all: eauto using conv_substs_up.
      - eapply meta_conv_conv.
        + eapply IHht1; eauto using ctx_typing, typing.
          * eapply ConvSubst_morphism.
            5: eapply conv_substs_up. 5: eauto.
            2-4: reflexivity.
            1:reflexivity.
            econstructor; eauto.
          * eapply WellSubst_morphism.
            4: eapply WellSubst_up. 4: eauto.
            2-3: reflexivity.
            3:econstructor;eauto.
            all:reflexivity.
        + reflexivity.
      - eapply meta_conv_conv.
        + eauto.
        + rasimpl. reflexivity.
      - eapply meta_conv_conv.
        + eapply IHht3; eauto using ctx_typing, typing.
          * eapply ConvSubst_morphism.
            5: eapply conv_substs_up.
            5: eapply conv_substs_up.
            all:eauto using typing. all:eauto. 1,2:reflexivity.
          * eapply WellSubst_morphism.
            4:eapply WellSubst_up. 4:eapply WellSubst_up.
            all:eauto using typing. reflexivity.
        + rasimpl. reflexivity.
    }
    rasimpl. reflexivity.
  - eapply conv_conv. 1: eauto.
    eapply meta_conv_conv.
    { eapply typing_conversion_subst. all: eauto. }
    reflexivity.
Qed.

Lemma validity_gen :
  (∀ Γ l t A,
    Γ ⊢< l > t : A →
    ⊢ Γ →
    Γ ⊢< Ax l > A : Sort l
  ) ∧
  (∀ Γ l u v A,
    Γ ⊢< l > u ≡ v : A →
    ⊢ Γ →
    Γ ⊢< l > u : A ∧ Γ ⊢< l > v : A).
Proof.
  apply typing_mutind.
  all: try solve [ intros ; econstructor ; eauto ].
  all: try solve [
    intros ; try econstructor ; try econstructor ; intuition eauto
  ].
  - eauto using valid_varty.
  - intros.
    eapply meta_conv.
    { eapply typing_conversion_subst.
      all: eauto using subst_one.
    }
    reflexivity.
  - intros. eapply meta_lvl; eauto using typing.
  - intros.
    eapply meta_conv.
    { eapply typing_conversion_subst.
      all: eauto using subst_one.
    }
    reflexivity.
  - intros. intuition eauto.
  - intros Γ i j A B **.
    assert (⊢ Γ ,, (i,A)).
    { intuition eauto using ctx_cons. }
    split ; econstructor. all: intuition eauto.
    eapply typing_ctx_conv. 1,2: eauto using ctx_typing.
    constructor. 1: eauto using ctx_conv_refl.
    apply conv_sym. assumption.
  - intros Γ i j A B **.
    assert (⊢ Γ ,, (i,A)).
    { intuition eauto using ctx_cons. }
    split.
    + econstructor. all: intuition eauto.
    + econstructor.
      * {
        econstructor. 1: intuition eauto.
        all: intuition eauto 9 using typing_ctx_conv, ctx_conv_refl, conv_ccons, conv_sym, ctx_typing.
        eapply typing_ctx_conv.
        - eapply type_conv. all: intuition eauto.
        - all: intuition eauto using ctx_conv_refl, conv_ccons, conv_sym, ctx_typing.
        - econstructor; eauto using conv_sym, ctx_conv_refl.
      }
      * apply conv_sym. constructor.
        all: intuition eauto.
  - intros Γ i j A B **.
    assert (⊢ Γ ,, (i,A)).
    { intuition eauto using ctx_cons. }
    split.
    + econstructor. all: intuition eauto.
    + eapply type_conv.
      * {
        econstructor. 1: intuition eauto.
        all: intuition eauto 9 using type_conv, typing_ctx_conv, ctx_conv_refl, conv_ccons, conv_sym, ctx_typing.
        eapply type_conv. 1: intuition eauto.
        constructor. all: intuition eauto.
      }
      * {
        apply conv_sym. eapply conv_trans.
        - eapply meta_conv_conv.
          + eapply typing_conversion_subst.
            all: intuition eauto using subst_one.
          + reflexivity.
        - eapply meta_conv_conv.
          { eapply conv_substs.
            - eauto.
            - eapply substs_one. eauto.
            - eapply subst_one. intuition eauto.
            - intuition eauto.
          }
          reflexivity.
      }
  - intros Γ l P **.
    assert (⊢ Γ ,, (ty 0, Nat)).
    { eapply ctx_cons. 1: assumption.
      econstructor. assumption.
    }
    assert (⊢ (Γ ,, (ty 0, Nat)) ,, (l, P)).
    { eapply ctx_cons. 1: assumption.
      intuition eauto.
    }
    split.
    + econstructor. all: intuition eauto.
    + eapply type_conv.
      * {
        econstructor. all: intuition eauto.
        - eapply type_conv. 1: intuition eauto.
          eapply meta_conv_conv.
          + eapply typing_conversion_subst. 1,2: intuition eauto.
            eapply well_scons_alt.
            * apply subst_id. assumption.
            * cbn. constructor. assumption.
          + reflexivity.
        - eapply typing_ctx_conv.
          + eapply type_conv. 1: intuition eauto.
            eapply meta_conv_conv.
            * {
              eapply typing_conversion_subst. 1: intuition eauto.
              1:econstructor; eauto.
              eapply well_scons_alt.
              - change (↑ >> (↑ >> var)) with (var >> ren_term S >> ren_term S).
                eapply WellSubst_weak.
                1:eapply WellSubst_weak.
                1:apply subst_id; eauto.
                1,2:eauto using typing.
              - cbn. constructor.
                eapply meta_conv.
                + repeat constructor. all:eauto.
                + reflexivity.
            }
            * reflexivity.
          + constructor. 1: eauto using ctx_conv_refl. eauto.
          + econstructor; eauto using ctx_conv_refl, conv_sym.     
      }
      * {
        apply conv_sym. eapply conv_trans.
        - eapply meta_conv_conv.
          + eapply typing_conversion_subst.
            all: intuition eauto using subst_one.
          + reflexivity.
        - eapply meta_conv_conv.
          { eapply conv_substs.
            - eauto.
            - eapply substs_one. eauto.
            - eapply subst_one. intuition eauto.
            - intuition eauto.
          }
          reflexivity.
      }
  - intros Γ i j A B **.
    assert (⊢ Γ ,, (i,A)).
    { intuition eauto using ctx_cons. }
    split.
    + econstructor. all: intuition eauto.
      econstructor. all: intuition eauto.
    + eapply typing_conversion_subst. all: eauto using subst_one.
  - intros Γ l P **.
    assert (⊢ Γ ,, (ty 0, Nat)).
    { eapply ctx_cons. 1: assumption.
      econstructor. assumption.
    }
    assert (⊢ (Γ ,, (ty 0, Nat)) ,, (l, P)).
    { eapply ctx_cons. 1: assumption.
      intuition eauto.
    }
    split.
    + econstructor. all: intuition eauto.
      econstructor. assumption.
    + auto.
  - intros Γ l P **.
    assert (⊢ Γ ,, (ty 0, Nat)).
    { eapply ctx_cons. 1: assumption.
      econstructor. assumption.
    }
    assert (⊢ (Γ ,, (ty 0, Nat)) ,, (l, P)).
    { eapply ctx_cons. 1: assumption.
      intuition eauto.
    }
    split.
    + econstructor. all: intuition eauto.
      econstructor. auto.
    + eapply meta_conv.
      { eapply typing_conversion_subst.
        - eauto.
        - assumption.
        - eapply well_scons_alt.
          + apply subst_one. assumption.
          + econstructor. all: intuition eauto.
      }
      rasimpl. reflexivity.
  - intros.
    split. all: intuition eauto.
  - intros.
    split. all: intuition eauto.
Qed.


Theorem refl_ctx : forall Γ, ⊢ Γ -> ⊢ Γ ≡ Γ.
Admitted.

Theorem wk_ty : forall Γ Δ l t A ρ, ⊢ Δ -> Γ ⊢< l > t : A -> ρ : Γ ⊆ Δ -> Δ ⊢< l > (wk_tm ρ t) : (wk_tm ρ A). (* why t ⟨ ρ ⟩ doesnt work ? *)
Admitted.

Theorem wk_conv : forall Γ Δ l t u A ρ, ⊢ Δ -> Γ ⊢< l > t ≡ u : A -> ρ : Γ ⊆ Δ -> Δ ⊢< l > (wk_tm ρ t) ≡ (wk_tm ρ u) : (wk_tm ρ A).
Admitted.

Theorem subst : forall Γ l t u A Δ σ τ, Δ ⊢s σ ≡ τ : Γ -> Γ ⊢< l > t ≡ u : A -> Δ ⊢< l > t <[ σ ] ≡ u <[ τ ] : A <[ σ ].
Admitted.


Theorem subst2 : forall Γ l t A Δ σ, Δ ⊢s σ : Γ -> Γ ⊢< l > t : A -> Δ ⊢< l > t <[ σ ] : A <[ σ ].
Admitted.


Corollary subst_ty : forall Γ l t u l' Δ σ, Δ ⊢s σ : Γ -> Γ ⊢< l > t ≡ u : Sort l' -> Δ ⊢< l > t <[ σ ] ≡ u <[ σ ] : Sort l'.
Admitted.


Corollary subst_ty' : forall Γ l t l' Δ σ, Δ ⊢s σ : Γ -> Γ ⊢< l > t : Sort l' -> Δ ⊢< l > t <[ σ ] : Sort l'.
Admitted.


Theorem conv_in_ctx_ty : forall Γ Δ l t A, ⊢ Γ ≡ Δ -> Γ ⊢< l > t : A -> Δ ⊢< l > t : A.
Admitted.

Theorem conv_in_ctx_conv : forall Γ Δ l t u A, ⊢ Γ ≡ Δ -> Γ ⊢< l > t ≡ u : A -> Δ ⊢< l > t ≡ u : A.
Admitted.

Theorem validity_ty : forall Γ l t A, Γ ⊢< l > t : A -> (⊢ Γ) /\ (Γ ⊢< Ax l > A : Sort l).
Admitted.

Theorem validity_ty_ctx : forall Γ l t A, Γ ⊢< l > t : A -> ⊢ Γ.
Admitted.

Theorem validity_ty_ty : forall Γ l t A, Γ ⊢< l > t : A -> Γ ⊢< Ax l > A : Sort l.
Admitted.

Theorem validity_conv : forall Γ l t u A, Γ ⊢< l > t ≡ u : A -> (Γ ⊢< l > t : A) /\ (Γ ⊢< l > u : A).
Admitted.

Theorem validity_conv_left : forall Γ l t u A, Γ ⊢< l > t ≡ u : A -> Γ ⊢< l > t : A.
Admitted.


Theorem validity_conv_right : forall Γ l t u A, Γ ⊢< l > t ≡ u : A -> Γ ⊢< l > u : A.
Admitted.

Theorem type_unicity : forall Γ l l' t A B, Γ ⊢< l > t : A ->  Γ ⊢< l' > t : B -> Γ ⊢< Ax l > A ≡ B : Sort l.
Admitted.

Theorem sort_unicity : forall Γ l l' t A B, Γ ⊢< l > t : A ->  Γ ⊢< l' > t : B -> l = l'.
Admitted.


Lemma conv_ctx_var Γ x l A Δ :
  Γ ∋< l > x : A →
  ⊢ Γ ≡ Δ ->
  ∃ B, Δ ∋< l > x : B ∧ Γ ⊢< Ax l > A ≡ B : Sort l.
Proof.
  intros hx hctx.
  induction hctx as [| Γ B Δ C i h ih] in l, x, A, hx |- *.
  - inversion hx.
  - inversion hx.
    + subst. eexists. split.
      * constructor.
      * admit.
    + subst. specialize ih with (1 := ltac:(eassumption)).
      destruct ih as (A & hA & he).
      eexists. split.
      * constructor. eassumption.
      * admit.
Admitted.


(* composite lemmas, for helping automation *)

Lemma conv_ty_in_ctx_conv Γ l A A' l' t u B :
  Γ ,, (l , A) ⊢< l' > t ≡ u : B ->
  Γ ⊢< Ax l > A ≡ A' : Sort l ->
  Γ ,, (l , A') ⊢< l' > t ≡ u : B.
Proof.
  intros t_eq_u A_eq_A'.
  eapply conv_in_ctx_conv; eauto.
  apply conv_ccons; eauto using refl_ctx, validity_ty_ctx, validity_conv_left.
Qed.


Lemma conv_ty_in_ctx_ty Γ l A A' l' t B :
  Γ ,, (l , A) ⊢< l' > t : B ->
  Γ ⊢< Ax l > A ≡ A' : Sort l ->
  Γ ,, (l , A') ⊢< l' > t : B.
Proof.
  intros t_eq_u A_eq_A'.
  eapply conv_in_ctx_ty; eauto.
  apply conv_ccons; eauto using refl_ctx, validity_ty_ctx, validity_conv_left.
Qed.


Lemma aux_subst_1 Γ l t A :
  Γ ⊢< l > t : A ->
  Γ ⊢s t .. : (Γ ,, (l, A)).
Proof.
  intro kWt.
  apply well_scons; ssimpl; eauto using validity_ty_ctx, subst_id.
Qed.

(* the following lemma helps automation to type some substitutions that appear often in the proof *)
Lemma aux_subst_2 Γ l P :
  Γ ,, (ty 0, Nat) ⊢< Ax l > P : Sort l ->
  (Γ,, (ty 0, Nat)),, (l, P) ⊢s (succ (var 1) .: ↑ >> (↑ >> var)) : Γ ,, (ty 0, Nat).
Proof.
  intro H.
  apply well_scons.
  - ssimpl. admit. (* by weakening *)
  - ssimpl. apply type_succ. apply (type_var _ 1 _ Nat); eauto. eauto using validity_ty_ctx, ctx_cons.
Admitted.


(* newer versions of inversion lemmas.
   TODO: replace in Confluence.v the occurrences of older inversion lemmas by the newer ones *)

Lemma type_inv_var' Γ l x T :
  Γ ⊢< l > var x : T →
  Γ ⊢< l > var x : T ∧ ∃ A, Γ ∋< l > x : A ∧ Γ ⊢< Ax l > T ≡ A : Sort l.
Proof.
  intro H.
  apply validity_ty_ty in H as T_Wt.
  split. auto.
  dependent induction H.
  - eexists. split; eauto using conv_refl.
  - edestruct IHtyping as (C & eq & A_eq_C); eauto using validity_conv_left. eexists. split; eauto using conv_trans, conv_sym.
Qed.

Lemma type_inv_sort' Γ l' i T:
  Γ ⊢< l' > Sort i : T ->
  Γ ⊢< l' > Sort i : T /\
  l' = Ax (Ax i) /\
  Γ ⊢< Ax (Ax (Ax i)) > T ≡ Sort (Ax i) : Sort (Ax (Ax i)).
Proof.
  intro H.
  apply validity_ty_ty in H as T_Wt.
  split. auto.
  dependent induction H.
  - repeat split; eauto using conv_refl.
  - edestruct IHtyping as (l_eq & conv); eauto using validity_conv_left.
    rewrite l_eq in *. repeat split; eauto using conv_trans, conv_sym.
Qed.

Lemma type_inv_pi' Γ l' i j A B T:
  Γ ⊢< l' > Pi i j A B : T ->
  Γ ⊢< l' > Pi i j A B : T /\
  Γ ⊢< Ax i > A : Sort i /\
  Γ ,, (i, A) ⊢< Ax j > B : Sort j /\
  l' = Ax (Ru i j) /\
  Γ ⊢< Ax (Ax (Ru i j)) > T ≡ Sort (Ru i j) : Sort (Ax (Ru i j)).
Proof.
  intro H.
  apply validity_ty_ty in H as T_Wt.
  split. auto.
  dependent induction H.
  - repeat split; eauto using conv_refl.
  - edestruct IHtyping as (AWt & BWt & l_eq & conv); eauto using validity_conv_left.
    rewrite l_eq in *. repeat split; eauto using conv_trans, conv_sym.
Qed.

Lemma type_inv_lam' Γ i j A B t T l :
      Γ ⊢< l > lam i j A B t : T ->
      Γ ⊢< l > lam i j A B t : T /\
      Γ ⊢< Ax i > A : Sort i /\
      Γ ,, (i , A) ⊢< Ax j > B : Sort j /\
      Γ ,, (i , A) ⊢< j > t : B /\
      l = Ru i j /\
      Γ ⊢< Ax (Ru i j) > T ≡ Pi i j A B : Sort (Ru i j).
Proof.
  intro H.
  apply validity_ty_ty in H as T_Wt.
  split. auto.
  dependent induction H; eauto.
  - repeat split; eauto using conv_refl.
  - edestruct IHtyping as (AWt & BWt & tWt & l_eq & conv); eauto using validity_conv_left.
    rewrite l_eq in *. repeat split; eauto using conv_trans, conv_sym.
Qed.

Lemma type_inv_app' Γ i j A B t u l T :
      Γ ⊢< l > app i j A B t u : T ->
      Γ ⊢< l > app i j A B t u : T /\
      Γ ⊢< Ax i > A : Sort i /\
      Γ ,, (i , A) ⊢< Ax j > B : Sort j /\
      Γ ⊢< Ru i j > t : Pi i j A B /\
      Γ ⊢< i > u : A /\
      l = j /\
      Γ ⊢< Ax j > T ≡ B <[ u.. ] : Sort j.
Proof.
  intro H.
  apply validity_ty_ty in H as T_Wt.
  split. auto.
  dependent induction H; eauto.
  - repeat split; eauto using conv_refl.
  - edestruct IHtyping as (AWt & BWt & tWt & uWt & l_eq & conv); eauto using validity_conv_left.
    rewrite l_eq in *. repeat split; eauto using conv_trans, conv_sym.
Qed.

Lemma type_inv_nat' Γ l' T:
  Γ ⊢< l' > Nat : T ->
  Γ ⊢< l' > Nat : T /\
  l' = ty 1 /\
  Γ ⊢< ty 2 > T ≡ Sort (ty 0) : Sort (ty 1).
Proof.
  intro H.
  apply validity_ty_ty in H as T_Wt.
  split. auto.
  dependent induction H.
  - repeat split; eauto using conv_refl.
  - edestruct IHtyping as (l_eq & conv); eauto using validity_conv_left.
    rewrite l_eq in *. repeat split; eauto using conv_trans, conv_sym.
Qed.


Lemma type_inv_zero' Γ l' T:
  Γ ⊢< l' > zero : T ->
  Γ ⊢< l' > zero : T /\
  l' = ty 0 /\
  Γ ⊢< ty 1 > T ≡ Nat : Sort (ty 0).
Proof.
  intro H.
  apply validity_ty_ty in H as T_Wt.
  split. auto.
  dependent induction H.
  - repeat split; eauto using conv_refl.
  - edestruct IHtyping as (l_eq & conv); eauto using validity_conv_left.
    rewrite l_eq in *. repeat split; eauto using conv_trans, conv_sym.
Qed.


Lemma type_inv_succ' Γ t T l :
      Γ ⊢< l > succ t : T ->
      Γ ⊢< l > succ t : T /\
      Γ ⊢< ty 0 > t : Nat /\
      l = ty 0 /\
      Γ ⊢< ty 1 > T ≡ Nat : Sort (ty 0).
Proof.
  intro H.
  apply validity_ty_ty in H as T_Wt.
  split. auto.
  dependent induction H; eauto.
  - repeat split; eauto using conv_refl.
  - edestruct IHtyping as (tWt & l_eq & conv); eauto using validity_conv_left.
    rewrite l_eq in *. repeat split; eauto using conv_trans, conv_sym.
Qed.

Lemma type_inv_rec' Γ l' l P p_zero p_succ t T :
  Γ ⊢< l' > rec l P p_zero p_succ t : T ->
  Γ ⊢< l' > rec l P p_zero p_succ t : T /\
  Γ ,, (ty 0 , Nat) ⊢< Ax l > P : Sort l /\
  Γ ⊢< l > p_zero : P <[ zero .. ] /\
  Γ ,, (ty 0 , Nat) ,, (l , P) ⊢< l > p_succ : P <[ (succ (var 1)) .: (shift >> (shift >> var)) ] /\
  Γ ⊢< ty 0 > t : Nat /\
  l' = l /\
  Γ ⊢< Ax l > T ≡ P <[ t.. ] : Sort l.
Proof.
  intro H.
  apply validity_ty_ty in H as T_Wt.
  split. auto.
  dependent induction H; eauto.
  - repeat split; eauto using conv_refl.
  - edestruct IHtyping as (PWt & p_zeroWt & p_succWt & tWt & l_eq & conv); eauto using validity_conv_left.
    rewrite l_eq in *. repeat split; eauto using conv_trans, conv_sym.
Qed.
