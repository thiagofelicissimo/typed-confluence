(** * Typing *)

From Stdlib Require Import Utf8 List Arith Bool Lia Wellfounded.Inverse_Image Wellfounded.Inclusion.
From TypedConfluence.autosubst
Require Import core unscoped AST SubstNotations RAsimpl AST_rasimpl.
From TypedConfluence Require Import Util BasicAST Weakenings Contexts Typing BasicMetaTheory Confluence. (*  Env Inst. *)
From Stdlib Require Import Setoid Morphisms Relation_Definitions.
Require Import Stdlib.Program.Equality.
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
end.

Lemma erasure_prop t : erasure prop t = box.
Proof.
  induction t; eauto.
Qed.


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


Lemma aux1 f σ t l : 
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


Lemma aux2 f σ l1 l2 t1 t2 : 
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

Lemma erasure_subst_commutes Γ t A l σ : 
  Γ ⊢< l > t : A -> 
  forall f, refines (fun_of_ctx Γ) f ->
  erasure l (t <[ σ ]) = erasure l t <[ erasure_subst f σ ].
Proof.
  rename l into l_.
  generalize Γ. clear Γ.
  dependent induction t; intros Γ Wt Δ ref.
  all : destruct l_. 
  all : (try rewrite erasure_prop; try rewrite erasure_prop; eauto).
  - simpl. apply type_inv_var in Wt as (B & nth). 
    unfold erasure_subst. unfold refines in ref.
    epose proof (H := ref n n0).
    unfold fun_of_ctx in H.
    rewrite nth in H. 
    destruct (H eq_refl) as (k & eq).
    rewrite eq. apply erasure_irrel.
  - simpl. apply type_inv_pi in Wt as (AWt & BWt).
    f_equal.
    eauto using IHt1.
    ssimpl.
    transitivity ((erasure (Ax l0) t2) <[ (erasure (ty 0) (var 0)) .: erasure_subst Δ σ >> ren_term ↑]).
    2 : eauto.
    setoid_rewrite <- aux1.
    eapply IHt2.
    eauto.
    setoid_rewrite cons_ctx_commute.
    eauto using refines_cons.
    - rename t1 into A'. rename t2 into B'. rename t3 into v.  
    simpl. apply type_inv_lam in Wt as (AWt & BWt & vWt).
    f_equal. ssimpl.
    transitivity  ((erasure l0 v) <[ erasure (ty 0) (var 0) .: erasure_subst Δ σ >> ren_term ↑]).
    2 : eauto.
    setoid_rewrite <- aux1.
    eapply IHt3; eauto. setoid_rewrite cons_ctx_commute. eauto using refines_cons.
  - rename t1 into A'. rename t2 into B'. rename t3 into u. rename t4 into v.
    apply type_inv_app in Wt as (Awt & Bwt & uWt & vWt).
    simpl. f_equal; eauto.
  - apply type_inv_succ in Wt. 
    simpl. f_equal. eauto.
  - rename t1 into P. rename t2 into p_zero. rename t3 into p_succ. rename t4 into k.
    apply type_inv_rec in Wt as (PWt & p_zeroWt & p_succWt & kWt).
    simpl. f_equal; ssimpl; eauto.
    + transitivity ((erasure (Ax l) P) <[ erasure (ty 0) (var 0) .: erasure_subst Δ σ >> ren_term ↑]).
      2:eauto.
      setoid_rewrite <- aux1.
      eapply IHt1; eauto. setoid_rewrite cons_ctx_commute. eauto using refines_cons.
    + transitivity ((erasure l p_succ) <[ erasure (ty 0) (var 0) .: (erasure (ty 0) (var 1) .: erasure_subst Δ σ >> ren_term (↑ >> ↑))]).
      2: eauto.
      setoid_rewrite <- aux2.
      eapply IHt3; eauto. setoid_rewrite cons_ctx_commute. setoid_rewrite cons_ctx_commute. eauto using refines_cons.
Qed. 




Lemma SR_aux Γ l i j A B i' j' A' B' t u T : 
  Γ ⊢< l > app i j A B (lam i' j' A' B' t) u : T -> 
  i = i' /\ 
  j = j' /\ 
  l = j  /\
  Γ ⊢< Ax i > A ≡ A' : Sort i /\
  Γ ,, (i, A) ⊢< Ax j > B ≡ B' : Sort j /\
  Γ ,, (i, A) ⊢< j > t : B /\ 
  Γ ⊢< i > u : A.
Proof.
  intro Wt.
  pose proof (Wt' := Wt).
  apply type_inv_app in Wt as (A_Wt & B_Wt & lam_Wt & u_Wt).
  assert (Γ ⊢< j > app i j A B (lam i' j' A' B' t) u : B <[ u..]) as Wt'' by eauto using type_app.   
  eapply sort_unicity in Wt' as j_eq_l; eauto.  
  pose proof (lam_Wt1 := lam_Wt).
  apply type_inv_lam in lam_Wt as (A'_Wt & B'_Wt & t_Wt).
  assert (Γ ⊢< Ru i' j' > lam i' j' A' B' t : Pi i' j' A' B') as lam_Wt2 by eauto using type_lam.
  eapply type_unicity in lam_Wt1 as pi_eq_pi; eauto.
  apply conv_sym in pi_eq_pi.
  apply pi_inj in pi_eq_pi as (i_eq_i' & j_eq_j' & A_eq_A' & B_eq_B').
  repeat split; eauto.
  rewrite i_eq_i' in *.
  rewrite j_eq_j' in *.
  eauto using conv_ty_in_ctx_ty, type_conv, conv_sym.  
Qed.

Lemma SR_aux2 Γ l i j A B i' j' A' B' t u T : 
  Γ ⊢< l > app i j A B (lam i' j' A' B' t) u : T -> 
  Γ ⊢< l > app i j A B (lam i' j' A' B' t) u ≡ t <[u .. ] : B <[ u..].
Proof.
  intro Wt.
  pose proof Wt as temp.
  apply type_inv_app in temp as (_ & _ & lamWt & _).
  apply SR_aux in Wt as (i_eq_i' & j_eq_j' & l_eq_j & A_eq_A' & B_eq_B' & tWt & uWt).
  rewrite i_eq_i' in *. clear i_eq_i' i.
  rewrite j_eq_j' in *. clear j_eq_j' j.
  rewrite l_eq_j in *. clear l_eq_j l.
  eapply conv_trans.
  eapply conv_app; eauto using refl_ty.
  eapply conv_conv.
  2: eapply subst_ty; eauto using aux_subst_1, conv_sym.
  eapply conv_beta; eauto using type_conv, validity_conv_right, conv_ty_in_ctx_ty.
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
  1-5 : dependent destruction erased_t_red_u.
  1-5,8-11: (
  try destruct (IHtWt1 ltac:(eauto using case_lvl) _ erased_t_red_u) as (X & conv & eq);
  try destruct (IHtWt2 ltac:(eauto using case_lvl) _ erased_t_red_u) as (X & conv & eq);
  try destruct (IHtWt3 ltac:(eauto using case_lvl) _ erased_t_red_u) as (X & conv & eq);
  try destruct (IHtWt4 ltac:(eauto using case_lvl) _ erased_t_red_u) as (X & conv & eq);
  eexists; split; [ eauto using conv_pi, conv_lam, conv_app, conv_succ, conv_rec, refl_ty 
                | rewrite <- eq; rewrite l_eq_n; eauto ]).

  (* case beta *)
  - destruct t. all : (rewrite l_eq_n in x; inversion x). clear x H0 t0.
    rename l into i'. rename l0 into j'. rename t1 into A'.
    rename t2 into B'. rename t3 into v.
    exists (v <[ u..]). split.
    ++ assert (Γ ⊢< j > app i j A B (lam i' j' A' B' v) u : B <[ u..]) by eauto using type_app. eauto using SR_aux2.
    ++ pose proof tWt3 as K. 
      apply type_inv_lam in tWt3 as (K1 & K2 & K3).
      assert (Γ ⊢< Ru i' j' > lam i' j' A' B' v : Pi i' j' A' B') by eauto using type_lam.
      eapply type_unicity in K; eauto.
      eapply pi_inj in K as (l_eq_i & l0_eq_n & _). 
      rewrite l0_eq_n in *. rewrite l_eq_i in *.
      erewrite erasure_subst_commutes; eauto. 
      +++ setoid_rewrite erasure_aux. eauto.
      +++ setoid_rewrite cons_ctx_commute. apply refines_cons2. apply refines_all.

  (* case succ cong *)
  (* TODO: further investigate why succ cong case must be done seperately *)
  - destruct (IHtWt ltac:(eauto using case_lvl) _ erased_t_red_u) as (X & conv & eq).
    eexists; split.
    + eauto using conv_succ, refl_ty.
    + rewrite <- eq. rewrite l_eq_n. simpl. f_equal. apply erasure_irrel.

  (* case rec zero *)
  - destruct t.  all : inversion x. clear x.
    exists p_zero. split; eauto using conv_rec_zero.

  (* case rec succ *)
  - destruct t. all : inversion x. clear x H0 n0.
    exists (p_succ <[ rec l P p_zero p_succ t .: t ..]).
    split.
    + apply type_inv_succ in tWt4. eauto using conv_rec_succ.
    + erewrite erasure_subst_commutes.
      ++ setoid_rewrite (erasure_cons (ty 0)). setoid_rewrite (erasure_cons (ty 0)). setoid_rewrite erasure_id. reflexivity.
      ++ eauto.
      ++ setoid_rewrite cons_ctx_commute. setoid_rewrite cons_ctx_commute. 
        apply refines_cons. apply refines_cons. apply refines_all.

  (* case conv *)
  - edestruct IHtWt.
    + right. eauto.
    + rewrite l_eq_n. eauto.
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
  - exists t0. split; eauto using refl_ty.
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

Definition nf t := forall u, t ---> u -> False.

Definition is_elim t := 
  match t with 
  | var _ => True
  | app _ _ _ _ _ _ => True
  | rec _ _ _ _ _ => True 
  | _ => False
end.

Definition ne t := nf t /\ is_elim t.


(* the following two results should be shown by mutual induction *)
Lemma eq_erased_nf Γ l t u A : 
  Γ ⊢< l > t : A -> 
  Γ ⊢< l > u : A ->
  nf (erasure l t) ->
  nf (erasure l u) ->
  erasure l t = erasure l u ->
  Γ ⊢< l > t ≡ u : A.
Admitted.

Lemma eq_erased_ne Γ i j t u A A' : 
  Γ ⊢< ty i > t : A -> 
  Γ ⊢< ty j > u : A' ->
  ne (erasure (ty i) t) ->
  ne (erasure (ty j) u) ->
  erasure (ty i) t = erasure (ty j) u ->
  Γ ⊢< ty i > t ≡ u : A.
Admitted.

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
  rewrite <- erased_t''_eq_t' in *. clear erased_t''_eq_t' t'.
  rewrite <- erased_u''_eq_u' in *. clear erased_u''_eq_u' u'.
  apply validity_conv_right in t_eq_t'' as t''_wt.
  apply validity_conv_right in u_eq_u'' as u''_wt.
  eapply eq_erased_nf in t'_eq_u'; eauto.
  eauto using conv_sym, conv_trans.
Qed.


Lemma ortho_red_to_red Γ l t t' A : 
  Γ ⊢< l > t ⟹ t' : A ->
  nf (erasure l t) -> erasure l t = erasure l t'.
Proof.
  intros t_red_t' nf_t.
  assert (l = prop \/ exists i, l = ty i) as case_l by (destruct l; eauto).
  induction t_red_t'.
  all : (destruct case_l as [H1 | H2]; try rewrite H1; eauto using erasure_prop, eq_sym, eq_trans).
  all : (destruct H2 as (l' & H2); rewrite H2 in *; simpl).
  - unfold nf in *. f_equal.  
    + apply IHt_red_t'1; eauto using case_lvl, nf_t, red_pi_1.
    + apply IHt_red_t'2; eauto using case_lvl, nf_t, red_pi_2.
  - unfold nf in *. f_equal.  
    apply IHt_red_t'; eauto using case_lvl, nf_t, red_lam.
  - unfold nf in *. f_equal.  
    + apply IHt_red_t'1; eauto using case_lvl, nf_t, red_app_1.
    + apply IHt_red_t'2; eauto using case_lvl, nf_t, red_app_2.
  - unfold nf in *. inversion H2. rewrite <- H0 in *. f_equal.  
    + apply IHt_red_t';  eauto using case_lvl, nf_t, red_succ.
  - unfold nf in *. f_equal.  
    + apply IHt_red_t'1; eauto using case_lvl, nf_t, red_rec_1.
    + apply IHt_red_t'2; eauto using case_lvl, nf_t, red_rec_2.
    + apply IHt_red_t'3; eauto using case_lvl, nf_t, red_rec_3.
    + apply IHt_red_t'4; eauto using case_lvl, nf_t, red_rec_4.
  - exfalso. eapply nf_t. simpl. eauto using red_beta.
  - exfalso. eapply nf_t. simpl. eauto using red_rec_zero.
  - exfalso. eapply nf_t. simpl. eauto using red_rec_succ.
Qed.

Lemma ortho_redd_to_red Γ l t t' A : 
  Γ ⊢< l > t ⟹* t' : A ->
  nf (erasure l t) -> erasure l t = erasure l t'.
Proof.
  intros t_redd_t' t_nf.
  induction t_redd_t'.
  - eauto using ortho_red_to_red.
  - apply IHt_redd_t'1 in t_nf as erased_t_eq_erased_v.
    rewrite erased_t_eq_erased_v in *.
    apply IHt_redd_t'2 in t_nf as erased_t_eq_erased_u.
    eauto.
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
  apply ortho_redd_to_red in t''_red_v; eauto.
  apply ortho_redd_to_red in u''_red_v; eauto.
  etransitivity; eauto.
Qed.

Corollary convcheck_correct Γ l t t' u u' A : 
  Γ ⊢< l > t : A -> erasure l t -->> t' -> nf t' ->
  Γ ⊢< l > u : A -> erasure l u -->> u' -> nf u' ->
  t' = u' <-> Γ ⊢< l > t ≡ u : A.
Proof.
  intros. split; eauto using convcheck_sound, convcheck_complete.
Qed.