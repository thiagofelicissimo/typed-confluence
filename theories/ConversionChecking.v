(** * Typing *)

From Stdlib Require Import Utf8 List Arith Bool Lia Wellfounded.Inverse_Image Wellfounded.Inclusion.
From TypedConfluence.autosubst
Require Import core unscoped AST SubstNotations RAsimpl AST_rasimpl.
From TypedConfluence Require Import Util BasicAST Weakenings Contexts Typing BasicMetaTheory Confluence. (*  Env Inst. *)
From Stdlib Require Import Setoid Morphisms Relation_Definitions.
Require Import Stdlib.Program.Equality.
Import CombineNotations.

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


Theorem subject_reduction Γ l t A u :
  Γ ⊢< l > t : A -> 
  erasure l t ---> u ->
  exists u', Γ ⊢< l > t ≡ u' : A /\ erasure l u' = u.
Admitted.

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

Lemma case_lvl l : l = prop \/ exists i, l = ty i.
Proof.
  destruct l; eauto.
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