(** * Typing *)

From Stdlib Require Import Utf8 List Arith Bool Lia Wellfounded.Inverse_Image Wellfounded.Inclusion.
From TypedConfluence
Require Import core unscoped Ast SubstNotations RAsimpl AST_rasimpl.
From TypedConfluence Require Import Util BasicAST Contexts Typing BasicMetaTheory Confluence.
From Stdlib Require Import Setoid Morphisms Relation_Definitions.
(* Require Import Stdlib.Program.Equality. *)
Require Import Equations.Prop.DepElim.
From Equations Require Import Equations.
Import CombineNotations.


(* I'm erasing levels to prop whenever they should be omitted.
   It would be less dirty to introduce a specific level 'null', like we introduced 'box' for omitted subterms *)
Fixpoint erasure l t : term :=
  match l, t with
  | prop, _ => box
  | ty _, var _ => t
  | ty _, Sort _ => t
  | ty _, Pi i j A B => Pi i j (erasure (Ax i) A) (erasure (Ax j) B)
  | ty _, lam i j A B t => lam prop prop box box (erasure j t)
  | ty _, app i j A B t u => app prop prop box box (erasure (Ru i j) t) (erasure i u)
  | ty _, Nat => t
  | ty _, zero => t
  | ty _, succ t => succ (erasure (ty 0) t)
  | ty _, rec l P p0 ps t => rec l (erasure (Ax l) P) (erasure l p0) (erasure l ps) (erasure (ty 0) t)
  | ty _, box => t
  | ty _, Eq i A a b => Eq i (erasure (Ax i) A) (erasure i a) (erasure i b)
  | ty _, J l i A a P p b e => J l i (erasure (Ax l) A) (erasure l a) (erasure (Ax i) P) (erasure i p) (erasure l b) box
end.

Lemma erasure_prop t : erasure prop t = box.
Proof.
  induction t; eauto.
Qed.


(* TODO: When adding Lean's eq, these are not normal forms anymore, because J is always a neutral,
  even if a and b are the same, which would allow for the term to reduce. Maybe it would be better to call them
  Chk and Inf, for checkable and inferable terms. The important property is that the typing annotations of Chk are
  uniquely determined when we know their types, whereas the typing annotations of Inf are always uniquely determined.
  But this could cause a confusion with the terms used by the bidirectional typing system. *)
Inductive Nf : term -> Prop :=
| nf_pi i j A B : Nf A -> Nf B -> Nf (Pi i j A B)
| nf_lam t : Nf t -> Nf (lam prop prop box box t)
| nf_sort l : Nf (Sort l)
| nf_nat : Nf Nat
| nf_zero : Nf zero
| nf_succ t : Nf t -> Nf (succ t)
| nf_ne t : Ne t -> Nf t
| nf_eq i A a b : Nf A -> Nf a -> Nf b -> Nf (Eq i A a b)
| nf_box : Nf box
with Ne : term -> Prop :=
| ne_var x : Ne (var x)
| ne_app t u : Ne t -> Nf u -> Ne (app prop prop box box t u)
| ne_rec l P p_zero p_succ t : Nf P -> Nf p_zero -> Nf p_succ -> Ne t -> Ne (rec l P p_zero p_succ t)
| ne_J l i A a P p b : Nf A -> Nf a -> Nf P -> Nf p -> Nf b -> Ne (J l i A a P p b box).

Scheme Nf_mut := Induction for Nf Sort Prop
with Ne_mut := Induction for Ne Sort Prop.
Combined Scheme Nf_Ne_mutind from Nf_mut, Ne_mut.

Reserved Notation "t ---> u" (at level 50, u at next level).

Inductive red : term -> term -> Prop :=
| red_pi_1 i j A A' B :
    A ---> A' ->
    Pi i j A B ---> Pi i j A' B

| red_pi_2 i j A B B' :
    B ---> B' ->
    Pi i j A B ---> Pi i j A B'

| red_app_1 t t' u :
    t ---> t' ->
    app prop prop box box t u ---> app prop prop box box t' u

| red_app_2 t u u' :
    u ---> u' ->
    app prop prop box box t u ---> app prop prop box box t u'

| red_lam t t' :
    t ---> t' ->
    lam prop prop box box t ---> lam prop prop box box t'

| red_succ t t' :
    t ---> t' ->
    succ t ---> succ t'

| red_rec_1 l P P' p_zero p_succ n :
    P ---> P' ->
    rec l P p_zero p_succ n ---> rec l P' p_zero p_succ n

| red_rec_2 l P p_zero p_zero' p_succ n :
    p_zero ---> p_zero' ->
    rec l P p_zero p_succ n ---> rec l P p_zero' p_succ n

| red_rec_3 l P p_zero p_succ p_succ' n :
    p_succ ---> p_succ' ->
    rec l P p_zero p_succ n ---> rec l P p_zero p_succ' n

| red_rec_4 l P p_zero p_succ n n' :
    n ---> n' ->
    rec l P p_zero p_succ n ---> rec l P p_zero p_succ n'

| red_beta t u :
    app prop prop box box (lam prop prop box box t) u ---> t <[ u.. ]

| red_rec_zero l P p_zero p_succ :
    rec l P p_zero p_succ zero ---> p_zero

| red_rec_succ l P p_zero p_succ n :
    rec l P p_zero p_succ (succ n) ---> p_succ <[  (rec l P p_zero p_succ n) .: n ..]

| red_eq_1 l A A' a b :
    A ---> A' ->
    Eq l A a b ---> Eq l A' a b

| red_eq_2 l A a a' b :
    a ---> a' ->
    Eq l A a b ---> Eq l A a' b

| red_eq_3 l A a b b' :
    b ---> b' ->
    Eq l A a b ---> Eq l A a b'

| red_J_1 l i A A' a P p b :
    A ---> A' ->
    J l i A a P p b box ---> J l i A' a P p b box

| red_J_2 l i A a a' P p b :
    a ---> a' ->
    J l i A a P p b box ---> J l i A a' P p b box

| red_J_3 l i A a P P' p b :
    P ---> P' ->
    J l i A a P p b box ---> J l i A a P' p b box

| red_J_4 l i A a P p p' b :
    p ---> p' ->
    J l i A a P p b box ---> J l i A a P p' b box

| red_J_5 l i A a P p b b' :
    b ---> b' ->
    J l i A a P p b box ---> J l i A a P p b' box

| red_J_refl l i A a P p :
    Nf a ->
    J l i A a P p a box ---> p

where "t ---> u" := (red t u).

Lemma case_lvl l : l = prop \/ exists i, l = ty i.
Proof.
  destruct l; eauto.
Qed.

Lemma erasure_irrel t i j : erasure (ty i) t = erasure (ty j) t.
Proof.
  destruct t; eauto.
Qed.

Definition erasure_subst (f : nat -> level) σ x := erasure (f x) (σ x).

Lemma erasure_rename_commute l t σ : erasure l (σ ⋅ t) = σ ⋅ erasure l t.
Proof.
  generalize l σ. clear l σ.
  induction t; intros l' σ.
  all: destruct l'.
  all: try rewrite erasure_prop; try rewrite erasure_prop; try eauto.
  all : simpl; ssimpl; f_equal; eauto.
Qed.


Definition rel_map_cons (f : nat -> level) l x :=
  match x with
  | 0 => l
  | S x => f x
end.

Reserved Notation "f ;; l" (at level 50, l at next level).
Notation "f ;; l" := (rel_map_cons f l).


Reserved Notation "A ~ B" (at level 50, B at next level).
Notation "A ~ B" := (pointwise_relation _ eq A B).


Lemma erasure_subst_cons f σ t l :
  erasure_subst (f ;; l) (t .: σ >> ren_term ↑) ~ (erasure l t .: erasure_subst f σ >> ren_term ↑).
Proof.
  intro x.
  destruct x.
  - ssimpl. unfold erasure_subst. simpl. reflexivity.
  - simpl. ssimpl.
    unfold erasure_subst.
    simpl. destruct x.
    + ssimpl. apply erasure_rename_commute.
    + simpl. rewrite <- erasure_rename_commute. simpl. reflexivity.
Qed.


Lemma erasure_subst_cons2 f σ l1 l2 t1 t2 :
  erasure_subst ((f ;; l2) ;; l1) (t1 .: (t2 .: σ >> ren_term (↑ >> ↑))) ~ (erasure l1 t1 .: (erasure l2 t2 .: erasure_subst f σ >> ren_term (↑ >> ↑))).
Proof.
  intro x.
  destruct x.
  - ssimpl. unfold erasure_subst. simpl. reflexivity.
  - destruct x.
    + ssimpl. unfold erasure_subst. simpl. reflexivity.
    + simpl. ssimpl.
      unfold erasure_subst.
      simpl. destruct x.
      ++ ssimpl. apply erasure_rename_commute.
      ++ simpl. rewrite <- erasure_rename_commute. simpl. reflexivity.
Qed.


Definition refines (f g : nat -> level) :=
  forall x i, f x = ty i -> exists j, g x = ty j.


Lemma refines_cons f g l i :
  refines f g -> refines (f ;; l) (g ;; (ty i)).
Proof.
  intro ref.
  unfold refines.
  intros.
  destruct x.
  - eexists. simpl. eauto.
  - simpl in H. apply ref in H as (j & eq).
    eexists. simpl. eauto.
Qed.


Definition fun_of_ctx (Δ : ctx) x :=
  match nth_error Δ x with
  | Some (l, _) => l
  | None => prop
end.


Lemma refines_preserves_eq f1 f2 g1 g2 :
  f1 ~ f2 -> g1 ~ g2 -> refines f1 g1 -> refines f2 g2.
Proof.
  intros feq geq P1.
  unfold refines in *. intros.
  rewrite <- geq.
  eapply P1.
  rewrite feq.
  eauto.
Qed.


From Stdlib Require Import Relation_Definitions.
From Stdlib.Classes Require Import CEquivalence.

Add Parametric Morphism : refines
  with signature ((pointwise_relation _ eq) ==> (pointwise_relation _ eq) ==> iff)
  as Phi_mor.
Proof.
  intros f₁ f₂ Hf g₁ g₂ Hg.
  split; eauto using refines_preserves_eq.
  apply refines_preserves_eq; apply pointwise_symmetric; eauto using eq_sym.
Qed.


Add Parametric Morphism : rel_map_cons
  with signature ((pointwise_relation _ eq) ==> eq ==> (pointwise_relation _ eq))
  as Phi_mor'.
Proof.
  intros f g eq l x.
  destruct x; eauto.
Qed.

Lemma cons_ctx_commute Γ l A : fun_of_ctx (Γ ,, (l, A)) ~ (fun_of_ctx Γ ;; l).
Proof.
  intro x.
  destruct x; reflexivity.
Qed.

Lemma varty_fun_of_ctx Γ l A x :
  Γ ∋< l > x : A →
  fun_of_ctx Γ x = l.
Proof.
  intros h.
  induction h. all: eauto.
Qed.

Lemma erasure_subst_commutes Γ t A l σ :
  Γ ⊢< l > t : A ->
  ∀ f, refines (fun_of_ctx Γ) f ->
  erasure l (t <[ σ ]) = erasure l t <[ erasure_subst f σ ].
Proof.
  rename l into l_.
  revert Γ.
  dependent induction t; intros Γ Wt Δ ref.
  all : destruct l_.
  all : (try rewrite erasure_prop; try rewrite erasure_prop; eauto).
  all: (simpl; apply type_inv in Wt; dependent destruction Wt).
  4,5,7: (f_equal;eauto).
  - unfold erasure_subst. unfold refines in ref.
    eapply varty_fun_of_ctx in var_in_ctx.
    eapply ref in var_in_ctx as (j & eq).
    rewrite eq.
    apply erasure_irrel.
  - f_equal. eauto using IHt1.  ssimpl.
    transitivity ((erasure (Ax l0) t2) <[ (erasure (ty 0) (var 0)) .: erasure_subst Δ σ >> ren_term ↑]); eauto.
    setoid_rewrite <- erasure_subst_cons.
    eapply IHt2; eauto.
    setoid_rewrite cons_ctx_commute.
    eauto using refines_cons.
  - f_equal. ssimpl.
    transitivity  ((erasure l0 t3) <[ erasure (ty 0) (var 0) .: erasure_subst Δ σ >> ren_term ↑]).
    2 : eauto.
    setoid_rewrite <- erasure_subst_cons.
    eapply IHt3; eauto. setoid_rewrite cons_ctx_commute. eauto using refines_cons.
  - f_equal; ssimpl; eauto.
    + transitivity ((erasure (Ax l) t1) <[ erasure (ty 0) (var 0) .: erasure_subst Δ σ >> ren_term ↑]).
      2:eauto.
      setoid_rewrite <- erasure_subst_cons.
      eapply IHt1; eauto. setoid_rewrite cons_ctx_commute. eauto using refines_cons.
    + transitivity ((erasure l t3) <[ erasure (ty 0) (var 0) .: (erasure (ty 0) (var 1) .: erasure_subst Δ σ >> ren_term (↑ >> ↑))]).
      2: eauto.
      setoid_rewrite <- erasure_subst_cons2.
      eapply IHt3; eauto. setoid_rewrite cons_ctx_commute. setoid_rewrite cons_ctx_commute. eauto using refines_cons.
  - subst. simpl. f_equal; eauto. 
    transitivity ((erasure (Ax (ty n)) t3) <[ erasure (ty 0) (var 0) .: erasure_subst Δ σ >> ren_term ↑]).
    2:eauto.
    setoid_rewrite <- erasure_subst_cons.
    eapply IHt3; eauto using refines_cons. setoid_rewrite cons_ctx_commute. eauto using refines_cons.
Qed.

Lemma erasure_aux i u : erasure_subst ((fun _ => ty 0) ;; i) (u ..) ~ ((erasure i u) ..).
Proof.
  intro x. destruct x.
  - reflexivity.
  - unfold erasure_subst. eauto.
Qed.


Lemma erasure_id : erasure_subst (fun _ => ty 0) var ~ var.
Proof.
  intro x. reflexivity.
Qed.

Lemma erasure_cons i f σ u : erasure_subst (f ;; i) (u .: σ ) ~ ((erasure i u) .: erasure_subst f σ).
Proof.
  intro x. destruct x.
  - reflexivity.
  - unfold erasure_subst. eauto.
Qed.


Lemma refines_cons2 f g l :
  refines f g -> refines (f ;; l) (g ;; l).
Proof.
  intro ref.
  unfold refines.
  intros.
  destruct x.
  - eexists. simpl. eauto.
  - simpl in H. apply ref in H as (j & eq).
    eexists. simpl. eauto.
Qed.


Lemma refines_all f : refines f (fun _ => ty 0).
Proof.
  unfold refines.
  intros.
  exists 0. reflexivity.
Qed.


Lemma erasure_subst_2_commutes Γ i A i' A' j v B u u' :
  Γ,, (i, A) ,, (i' , A') ⊢< j > v : B ->
  erasure j (v <[ u' .: (u ..)]) = (erasure j v) <[ (erasure i' u') .: ((erasure i u) ..)].
Proof.
  intro v_Wt.
  erewrite erasure_subst_commutes.
  - setoid_rewrite erasure_cons. setoid_rewrite erasure_cons. setoid_rewrite erasure_id. reflexivity.
  - eauto.
  - setoid_rewrite cons_ctx_commute. setoid_rewrite cons_ctx_commute.
    apply refines_cons2. apply refines_cons2. apply refines_all.
Qed.

Lemma erasure_subst_1_commutes Γ i A j v B u :
  Γ,, (i, A) ⊢< j > v : B ->
  erasure j (v <[ u..]) = (erasure j v) <[ (erasure i u)..].
Proof.
  intro v_Wt.
  erewrite erasure_subst_commutes; eauto.
      +++ setoid_rewrite erasure_aux. eauto.
      +++ setoid_rewrite cons_ctx_commute. apply refines_cons2. apply refines_all.
Qed.


Definition nf t := forall u, t ---> u -> False.

Definition is_elim t :=
  match t with
  | var _ => True
  | app _ _ _ _ _ _ => True
  | rec _ _ _ _ _ => True
  | _ => False
end.

Definition ne t := nf t /\ is_elim t.


Definition not_a_lam t :=
  match t with
  | lam _ _ _ _ _ => False
  | _ => True
end.

Lemma nf_pi_is_ne Γ l t i j A B :
  Γ ⊢< ty l > t : Pi i j A B ->
  Nf (erasure (ty l) t) -> not_a_lam t -> Ne (erasure (ty l) t).
Proof.
  intros t_Wt.
  induction t; intros  nf_et t_neq_lam; eauto using Nf, Ne.
  all: (eapply type_inv in t_Wt as temp; dependent destruction temp).
  3:inversion t_neq_lam.
  1,2,4,8: (eapply conv_sym, sort_neq_pi in conv_ty; intuition eauto).
  2,3: (eapply conv_sym, nat_neq_pi in conv_ty; intuition eauto).
  all: (inversion nf_et; eauto).
Qed.

Definition not_zero_or_succ t :=
  match t with
  | zero => False
  | succ _ => False
  | _ => True
end.

Lemma nf_nat_is_ne Γ l t :
  Γ ⊢< ty l > t : Nat ->
  Nf (erasure (ty l) t) -> not_zero_or_succ t -> Ne (erasure (ty l) t).
Proof.
  intros t_Wt.
  induction t; intros  nf_et t_neq_zero_or_succ; eauto using Nf, Ne.
  all: (eapply type_inv in t_Wt as temp; dependent destruction temp).
  all: (eapply type_inv in t_Wt as temp; dependent destruction temp).
  6,7:inversion t_neq_zero_or_succ.
  3:(eapply nat_neq_pi in conv_ty; intuition eauto).
  1,2,4,6: (eapply conv_sym, sort_neq_nat in conv_ty; intuition eauto).
  all:(inversion nf_et; eauto).
Qed.

Hint Unfold ConversionChecking.nf.

Lemma nf_to_Nf Γ l t A :
  Γ ⊢< l > t : A -> nf (erasure l t) -> Nf (erasure l t).
Proof.
  intros t_Wt nf. induction t_Wt.
  all: (match goal with | |- Nf (erasure ?l _) => pose (K := case_lvl l) end;
      destruct K as [l_eq_prop | (n & l_eq_n)];
      [rewrite l_eq_prop; rewrite erasure_prop; eauto using nf_box | idtac]).
  all: (try rewrite l_eq_n in *; try clear l).
  all: eauto 24 using Nf, Ne, red.
  - apply nf_ne. apply ne_app; eauto using red.
    eapply nf_pi_is_ne; eauto using red.
    destruct t; unfold not_a_lam; eauto. 
    eapply nf. simpl. eauto using red.
  - apply nf_succ. fold erasure. rewrite l_eq_n. apply IHt_Wt. unfold ConversionChecking.nf in *. intros. eapply nf. simpl. rewrite l_eq_n. eauto using red.
  - apply nf_ne. apply ne_rec; eauto using red.
    eapply nf_nat_is_ne; eauto using red.
    destruct t; unfold not_zero_or_succ; eauto.
    all: eapply nf; simpl; eauto using red.
Qed.

Lemma eq_erased_adjust_IH {l' t4} : 
  (∀ (Γ : ctx) (i : nat) (t u T : term), Γ ⊢< ty i > t : T → Γ ⊢< ty i > u : T → erasure (ty i) t = erasure (ty i) u
    → erasure l' t4 = erasure (ty i) t → Γ ⊢< ty i > t ≡ u : T) ->
  ∀ (Γ : ctx) l (t u T : term), Γ ⊢< l > t : T → Γ ⊢< l > u : T → erasure l t = erasure l u
    → erasure l' t4 = erasure l t → Γ ⊢< l > t ≡ u : T.
Proof.
  intros. destruct l; eauto using conv_irrel.
Qed.


Lemma eq_erased :
  (forall et, Nf et ->
    forall Γ i t0 u0 T
    (t0_Wt : Γ ⊢< ty i > t0 : T)
    (u0_Wt : Γ ⊢< ty i > u0 : T)
    (erased_t0_eq_erased_u0 : erasure (ty i) t0 = erasure (ty i) u0)
    (et_eq_erased_t0 : et = erasure (ty i) t0),
    Γ ⊢< ty i > t0 ≡ u0 : T)
    /\
  (forall et, Ne et ->
    forall Γ i i' t0 u0 T T'
    (t0_Wt : Γ ⊢< ty i > t0 : T)
    (u0_Wt : Γ ⊢< ty i' > u0 : T')
    (erased_t0_eq_erased_u0 : erasure (ty i) t0 = erasure (ty i') u0)
    (et_eq_erased_t0 : et = erasure (ty i) t0),
    Γ ⊢< ty i > t0 ≡ u0 : T).
Proof.
  apply Nf_Ne_mutind; intros.
  1-6, 8-13:(destruct t0; dependent destruction et_eq_erased_t0;
    destruct u0; dependent destruction erased_t0_eq_erased_u0;
    eapply type_inv in t0_Wt as temp; dependent destruction temp;
    eapply type_inv in u0_Wt as temp; dependent destruction temp;  subst).

  all: eauto using conv_refl.

  all: try (pose proof (H' := eq_erased_adjust_IH H); clear H).
  all: try (pose proof (H0' := eq_erased_adjust_IH H0); clear H0).
  all: try (pose proof (H1' := eq_erased_adjust_IH H1); clear H1).
  all: try (pose proof (H2' := eq_erased_adjust_IH H2); clear H2).
  all: try (pose proof (H3' := eq_erased_adjust_IH H3); clear H3).

  - rewrite lvl_eq0. 
    eapply conv_conv; eauto 6 using conv_sym, conv_pi, conv_ty_in_ctx_ty.
  - rename t0_1 into A. rename t0_2 into B. rename t0_3 into t.
    rename u0_1 into A'. rename u0_2 into B'. rename u0_3 into t'.
    rewrite lvl_eq. eapply conv_conv; eauto using conv_sym.
    rewrite <- lvl_eq in conv_ty. rewrite <- lvl_eq0 in conv_ty0.
    eassert (_ ⊢< _ > Pi l l0 A B ≡ Pi l1 l2 A' B' : _) as pi_eq_pi
      by eauto using conv_sym, conv_trans.
    apply pi_inj in pi_eq_pi as (l_eq_l1 & l0_eq_l2 & A_eq & B_eq).
    subst. apply conv_lam; eauto.
    destruct l2. 2:inversion lvl_eq.
    eauto 6 using conv_ty_in_ctx_ty, conv_sym, type_conv, conv_ty_in_ctx_conv.
  - dependent destruction lvl_eq.
    eapply conv_conv. 2: eauto using conv_sym.
    apply conv_succ. eauto.
  - dependent destruction lvl_eq.
    eapply conv_conv; eauto using conv_sym.
    eapply conv_Eq; eauto using conv_conv, conv_sym, type_conv.
  - rename t0_1 into A. rename t0_2 into B. rename t0_3 into t. rename t0_4 into u.
    rename u0_1 into A'. rename u0_2 into B'. rename u0_3 into t'. rename u0_4 into u'.  
    eapply conv_conv; eauto using conv_sym.
    assert (Γ ⊢< Ru l (ty i) > t ≡ t' : Pi l (ty i) A B) as t1_eq_t2 by eauto.
    eapply validity_conv_right, type_unicity in t1_eq_t2 as pi_eq_pi. 2:exact t_Wt0.
    eapply pi_inj in pi_eq_pi as (eq1 & eq2 & A_eq & B_eq).
    subst. dependent destruction eq2.
    eapply conv_app; eauto using type_conv, conv_sym, conv_ty_in_ctx_conv.
  - dependent destruction lvl_eq0.
    eapply conv_conv; eauto using conv_sym.
    eapply conv_rec; eauto.
    + eapply H0'; eauto 9 using type_conv, subst_conv, subst_one, validity_ty_ctx, type_zero, conv_sym, refl_subst.
    + eapply H1'; eauto. 
      eapply conv_ty_in_ctx_ty; eauto 8 using type_conv, subst_conv, subst_id_var1, ctx_from_conv, refl_subst.
  - eapply conv_conv; eauto using conv_sym.
    eapply conv_J; eauto using type_conv, conv_ty_in_ctx_ty. 
    + eapply H2'; eauto using type_conv, subst_conv, substs_one.
      eapply type_conv; eauto. 
      eapply subst_conv; eauto using validity_ty_ctx, substs_one, conv_refl, type_conv, conv_ty_in_ctx_ty.
    + eapply conv_irrel; eauto.
      eapply type_conv; eauto. eapply conv_Eq; eauto using type_conv, conv_ty_in_ctx_ty.
Qed.


Lemma eq_erased_nf Γ l t u A :
  Γ ⊢< l > t : A ->
  Γ ⊢< l > u : A ->
  nf (erasure l t) ->
  nf (erasure l u) ->
  erasure l t = erasure l u ->
  Γ ⊢< l > t ≡ u : A.
Proof.
  intros. destruct l.
  - eapply (proj1 eq_erased); eauto. eapply nf_to_Nf; eauto.
  - eauto using conv_irrel.
Qed.

Theorem subject_reduction Γ l t A u :
  Γ ⊢< l > t : A ->
  erasure l t ---> u ->
  exists u', Γ ⊢< l > t ≡ u' : A /\ erasure l u' = u.
Proof.
  intros tWt erased_t_red_u.
  assert (l = prop \/ exists i, l = ty i) as case_l by eauto using case_lvl.
  generalize  u erased_t_red_u. clear u erased_t_red_u.
  induction tWt; intros.

  all : destruct case_l as [l_eq_prop | (n & l_eq_n)];
    [ rewrite l_eq_prop in erased_t_red_u; rewrite erasure_prop in erased_t_red_u; inversion erased_t_red_u | idtac ].
  1,2,6,7: (rewrite l_eq_n in *; inversion erased_t_red_u).
  all : rewrite l_eq_n in erased_t_red_u at 1.
  1-7 : dependent destruction erased_t_red_u.
  1-5,8-11, 14-21: (
  try destruct (IHtWt1 ltac:(eauto using case_lvl) _ erased_t_red_u) as (X & conv & eq);
  try destruct (IHtWt2 ltac:(eauto using case_lvl) _ erased_t_red_u) as (X & conv & eq);
  try destruct (IHtWt3 ltac:(eauto using case_lvl) _ erased_t_red_u) as (X & conv & eq);
  try destruct (IHtWt4 ltac:(eauto using case_lvl) _ erased_t_red_u) as (X & conv & eq);
  try destruct (IHtWt5 ltac:(eauto using case_lvl) _ erased_t_red_u) as (X & conv & eq);
  try destruct (IHtWt6 ltac:(eauto using case_lvl) _ erased_t_red_u) as (X & conv & eq);
  eexists; split; [ eauto 13 using conv_pi, conv_lam, conv_app, conv_succ, conv_rec, conv_refl, conv_Eq, conv_J
                | rewrite <- eq; rewrite l_eq_n; eauto ]).

  all:subst.

  (* case beta *)
  - destruct t. all : inversion H. clear t0 H H1.
    rename l into i'. rename l0 into j'. rename t1 into A'.
    rename t2 into B'. rename t3 into v.
    eapply type_inv in tWt3 as temp; dependent destruction temp.
    eapply pi_inj in conv_ty as (eq1 & eq2 & A_conv_A' & B_conv_B'); subst.
    exists (v <[ u..]). split.
    * eapply conv_beta'; eauto.
    * eapply erasure_subst_1_commutes; eauto.

  (* case succ cong *)
  (* TODO: further investigate why succ cong case must be done seperately *)
  - destruct (IHtWt ltac:(eauto using case_lvl) _ erased_t_red_u) as (X & conv & eq).
    eexists; split.
    + eauto using conv_succ, conv_refl.
    + rewrite <- eq. rewrite l_eq_n. simpl. f_equal. apply erasure_irrel.

  (* case rec zero *)
  - destruct t.  all : inversion H. clear H.
    exists p_zero. split; eauto using conv_rec_zero.

  (* case rec succ *)
  - destruct t. all : inversion H. clear H H1 n0.
    exists (p_succ <[ rec (ty n) P p_zero p_succ t .: t ..]).
    split.
    + apply type_inv in tWt4. dependent destruction tWt4. eauto using conv_rec_succ.
    + erewrite erasure_subst_2_commutes; eauto. reflexivity.
    
  (* case J_refl *)
  - eexists. split.
    eapply conv_J_refl'; eauto. 2:eauto.
    destruct l. 2:eauto using conv_irrel. eapply (proj1 eq_erased) in H; eauto.

  (* case conv *)
  - edestruct IHtWt.
    + right. eauto.
    + eauto.
    + exists x. destruct H0 as (t_eq_x & erased_x_eq_u). split; eauto using conv_conv.
Qed.


Reserved Notation "t -->> u" (at level 50, u at next level).


Inductive redd : term -> term -> Prop :=
  | redd_refl t : t -->> t
  | redd_step t u : t ---> u -> t -->> u
  | redd_trans t u v : t -->> v -> v -->> u -> t -->> u
where "t -->> u" := (redd t u).



Lemma subject_reduction_redd_aux Γ l t t' A u' :
  Γ ⊢< l > t : A ->
  erasure l t = t' ->
  t' -->> u' ->
  exists u, Γ ⊢< l > t ≡ u : A /\ erasure l u = u'.
Proof.
  intros t_Wt erased_t_eq_t' t'_redd_u'.
  generalize t erased_t_eq_t' t_Wt. clear t erased_t_eq_t' t_Wt.
  induction t'_redd_u'; intros.
  - exists t0. split; eauto using conv_refl.
  - rewrite <- erased_t_eq_t' in *. eauto using subject_reduction.
  - rewrite <- erased_t_eq_t' in *. clear erased_t_eq_t' t.
    eapply IHt'_redd_u'1 in t_Wt as (v0 & t0_eq_v0 & erasure_v0_eq_v); eauto.
    apply validity_conv_right in t0_eq_v0 as v0_Wt.
    eapply IHt'_redd_u'2 in v0_Wt as (u0 & t0_eq_u0 & erasure_u0_eq_u); eauto.
    exists u0. split; eauto using conv_trans.
Qed.

Corollary subject_reduction_redd Γ l t A u :
  Γ ⊢< l > t : A ->
  erasure l t -->> u ->
  exists u', Γ ⊢< l > t ≡ u' : A /\ erasure l u' = u.
Proof.
  eauto using subject_reduction_redd_aux.
Qed.



Corollary convcheck_sound Γ l t u A t' u' :
  Γ ⊢< l > t : A ->
  Γ ⊢< l > u : A ->
  erasure l t -->> t' ->
  erasure l u -->> u' ->
  nf t' -> nf u' ->
  t' = u' ->
  Γ ⊢< l > t ≡ u : A.
Proof.
  intros t_wt u_wt t_redd u_redd t'_nf u'_nf t'_eq_u'.
  eapply subject_reduction_redd in t_redd as (t'' & t_eq_t'' & erased_t''_eq_t'); eauto.
  eapply subject_reduction_redd in u_redd as (u'' & u_eq_u'' & erased_u''_eq_u'); eauto.
  subst. 
  assert (nf (erasure l u'')) by 
    (rewrite erased_u''_eq_u'; assumption).
  eauto 7 using eq_erased_nf, conv_trans, conv_sym, validity_conv_right.
Qed.

(* TODO: add the following discussion to the paper
  Among the hypothesis of our theorem, we require the erasures of t and u to reduce to normal forms in order to conclude that t and u are convertible. Most proof assistants however implement an optimization which first checks for syntactic equality before normalizing the terms. In the presence of normalization, this optimization is sound, given that, if t and u are equal, then they will have normal forms which are also equal. Nevertheless, this optimization becomes unsound in systems like type-in-type: A counter-example is obtained by considering Howe's looping combinators, which are equal when erasing annotations, but not convertible (see the file X.v in the formalization for more details). Therefore, one must be careful to prove normalization in order to employ this optimization. On the other hand, it would be possible to drop the assumption of normalization if we considered an erased syntax with some annotations, such as domain annotations in lambdas. *)

Hint Unfold nf.


Lemma pre_ortho_redd_to_eq Γ l t t' A :
  (∀ l' u, size (erasure l' u) <= size (erasure l t) → 
    ∀ Γ t' A, Γ ⊢< l' > u ⟹ t' : A → nf (erasure l' u) → 
    erasure l' u = erasure l' t') ->
  Γ ⊢< l > t ⟹* t' : A ->
  nf (erasure l t) -> erasure l t = erasure l t'.
Proof.
  intros.
  induction H0.
  - eapply H in H0; eauto.
  - assert (erasure l t = erasure l v) by eauto.
    rewrite H0 in *.
    eapply IHortho_redd2; eauto.
Qed.

Lemma ortho_red_to_eq Γ l t t' A :
  Γ ⊢< l > t ⟹ t' : A ->
  nf (erasure l t) -> erasure l t = erasure l t'.
Proof.
  intros t_red_t' nf_t.

  assert (exists X, fst X = l /\ snd X = t ) as (X & eq1 & eq2).
    {exists ((l, t)). split; eauto. }
  rewrite <- eq1 in *. rewrite <- eq2 in *. clear eq1 eq2 t l.

  generalize X Γ t' A t_red_t' nf_t. clear X Γ t' A t_red_t' nf_t.
  refine (@well_founded_ind _ (fun X1 X2 => size (erasure (fst X1) (snd X1)) < size (erasure (fst X2) (snd X2))) _ _ _).
  eapply wf_inverse_image, lt_wf. intros. destruct x.
  simpl in *.

  assert (∀ l' u, size (erasure l' u) < size (erasure l t) → 
    ∀ Γ t' A, Γ ⊢< l' > u ⟹ t' : A → nf (erasure l' u) → erasure l' u = erasure l' t') 
      as IH by (intros; eapply (H (l', u)); eauto). clear H.

  destruct l. 2:rewrite erasure_prop; rewrite erasure_prop; reflexivity.
  dependent induction t_red_t'; eauto.
  all: (try clear IHt_red_t'1;try clear IHt_red_t'2;try clear IHt_red_t'3;try clear IHt_red_t'4;try clear IHt_red_t'5).
  all: simpl in nf_t.
  all: try (simpl; f_equal; eauto using nf_t, red;
    eapply IH; eauto using red; simpl; lia).
  all: try (exfalso; eapply nf_t; eauto using red).

  eapply CR in H0 as (w & red1 & red2).
  assert (nf (erasure l a)) by eauto using red.
  assert (nf (erasure l b)) by eauto using red.

  eapply pre_ortho_redd_to_eq in red1; eauto.
  2:intros; eapply IH; eauto; simpl in *; lia.

  eapply pre_ortho_redd_to_eq in red2; eauto.
  2:intros; eapply IH; eauto; simpl in *; lia.
  rewrite <- red1 in red2.
  rewrite red2.
  eapply red_J_refl.
  eapply validity_ty_ty, type_inv in H2. dependent destruction H2.
  eapply nf_to_Nf; eauto.
Qed.

Lemma ortho_redd_to_eq Γ l t t' A :
  Γ ⊢< l > t ⟹* t' : A ->
  nf (erasure l t) -> erasure l t = erasure l t'.
Proof.
  eapply pre_ortho_redd_to_eq.
  intros. eapply ortho_red_to_eq; eauto.
Qed.


Corollary convcheck_complete Γ l t t' u u' A :
  Γ ⊢< l > t ≡ u : A ->
  erasure l t -->> t' ->
  erasure l u -->> u' ->
  nf t' -> nf u' ->
  t' = u'.
Proof.
  intros t_eq_u t_redd_t' u_redd_u' nf_t' nf_u'.
  apply validity_conv_left in t_eq_u as t_wt.
  apply validity_conv_right in t_eq_u as u_wt.
  eapply subject_reduction_redd in t_redd_t' as (t'' & t_eq_t'' & erased_t''_eq_t'). 2: eauto.
  eapply subject_reduction_redd in u_redd_u' as (u'' & u_eq_u'' & erased_u''_eq_u'). 2: eauto.
  assert (Γ ⊢< l > t'' ≡ u'' : A) as t''_eq_u'' by eauto using conv_sym, conv_trans.
  rewrite <- erased_t''_eq_t' in *. clear erased_t''_eq_t' t'.
  rewrite <- erased_u''_eq_u' in *. clear erased_u''_eq_u' u'.
  apply CR in t''_eq_u'' as (v & t''_red_v & u''_red_v).
  apply ortho_redd_to_eq in t''_red_v; eauto.
  apply ortho_redd_to_eq in u''_red_v; eauto.
  etransitivity; eauto.
Qed.

Corollary convcheck_correct Γ l t t' u u' A :
  Γ ⊢< l > t : A -> erasure l t -->> t' -> nf t' ->
  Γ ⊢< l > u : A -> erasure l u -->> u' -> nf u' ->
  t' = u' <-> Γ ⊢< l > t ≡ u : A.
Proof.
  intros. split; eauto using convcheck_sound, convcheck_complete.
Qed.
