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
  | ty _, Sigma i j A B => Sigma i j (erasure (Ax i) A) (erasure (Ax j) B)
  | ty _, pair i j A B a b => pair prop prop box box (erasure i a) (erasure j b)
  | ty _, pi1 i j A B t => pi1 prop prop box box (erasure (Ru i j) t)
  | ty _, pi2 i j A B t => pi2 prop prop box box (erasure (Ru i j) t)
  | ty _, Nat => t
  | ty _, zero => t
  | ty _, succ t => succ (erasure (ty 0) t)
  | ty _, rec l P p0 ps t => rec l (erasure (Ax l) P) (erasure l p0) (erasure l ps) (erasure (ty 0) t)
  | ty _, box => t
  | ty _, Eq i A a b => Eq i (erasure (Ax i) A) (erasure i a) (erasure i b)
  | ty _, J l i A a P p b e => J l i (erasure (Ax l) A) (erasure l a) (erasure (Ax i) P) (erasure i p) (erasure l b) box
  | ty _, Lift i A => Lift i (erasure (Ax i) A)
  | ty _, lift i A a => lift prop box (erasure i a)
  | ty _, lower i A a => lower prop box (erasure (Ax i) a)
  | ty _, cast i A B e a => cast i (erasure (Ax i) A) (erasure (Ax i) B) box (erasure i a)
  | ty _, tysum i j A B => tysum i j (erasure (Ax i) A) (erasure (Ax j) B)
  | ty _, inl i j A B a => inl prop prop box box (erasure i a)
  | ty _, inr i j A B b => inr prop prop box box (erasure j b)
  | ty _, sum_case i j l A B P pl pr u => sum_case prop prop l box box (erasure (Ax l) P) (erasure l pl) (erasure l pr) (erasure (Ru i j) u)
  | _, _ => box (* junk branch *)
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
| nf_sigma i j A B : Nf A -> Nf B -> Nf (Sigma i j A B)
| nf_pair t u : Nf t -> Nf u -> Nf (pair prop prop box box t u)
| nf_sort l : Nf (Sort l)
| nf_nat : Nf Nat
| nf_zero : Nf zero
| nf_succ t : Nf t -> Nf (succ t)
| nf_ne t : Ne t -> Nf t
| nf_eq i A a b : Nf A -> Nf a -> Nf b -> Nf (Eq i A a b)
| nf_Lift i A : Nf A -> Nf (Lift i A)
| nf_lift a : Nf a -> Nf (lift prop box a)
| nf_sum i j A B : Nf A → Nf B → Nf (tysum i j A B)
| nf_inl a : Nf a → Nf (inl prop prop box box a)
| nf_inr b : Nf b → Nf (inr prop prop box box b)
| nf_box : Nf box
with Ne : term -> Prop :=
| ne_var x : Ne (var x)
| ne_app t u : Ne t -> Nf u -> Ne (app prop prop box box t u)
| ne_pi1 t : Ne t -> Ne (pi1 prop prop box box t)
| ne_pi2 t : Ne t -> Ne (pi2 prop prop box box t)
| ne_rec l P p_zero p_succ t : Nf P -> Nf p_zero -> Nf p_succ -> Ne t -> Ne (rec l P p_zero p_succ t)
| ne_J l i A a P p b : a <> b -> Nf A -> Nf a -> Nf P -> Nf p -> Nf b -> Ne (J l i A a P p b box)
| ne_lower t : Ne t -> Ne (lower prop box t)
| ne_cast1 i A B t : Ne A -> Nf B -> Nf t -> Ne (cast i A B box t)
| ne_cast2 i A B t : Nf A -> Ne B -> Nf t -> Ne (cast i A B box t)
| ne_cast3 i A B t : Nf A -> Nf B ->
    (* if both A, B are in nf, then they should not have
      the same relevant head in order for the result to be a neutral *)
    not (match A, B with
    | Pi i (ty n) _ _, Pi i' (ty n') _ _ => i = i' ∧ n = n'
    | Sort i, Sort i' => i = i'
    | Nat , Nat => True
    | _, _ => False
    end) -> Nf t -> Ne (cast i A B box t)
| ne_sum_case l P pl pr u :
    Nf P → Nf pl → Nf pr → Ne u →
    Ne (sum_case prop prop l box box P pl pr u)
.

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

| red_sigma_1 i j A A' B :
    A ---> A' ->
    Sigma i j A B ---> Sigma i j A' B

| red_sigma_2 i j A B B' :
    B ---> B' ->
    Sigma i j A B ---> Sigma i j A B'

| red_pair_1 t t' u :
    t ---> t' ->
    pair prop prop box box t u ---> pair prop prop box box t' u

| red_pair_2 t u u' :
    u ---> u' ->
    pair prop prop box box t u ---> pair prop prop box box t u'

| red_pi1 t t' :
    t ---> t' ->
    pi1 prop prop box box t ---> pi1 prop prop box box t'

| red_pi2 t t' :
    t ---> t' ->
    pi2 prop prop box box t ---> pi2 prop prop box box t'

| red_pi1pair t u :
    pi1 prop prop box box (pair prop prop box box t u) ---> t

| red_pi2pair t u :
    pi2 prop prop box box (pair prop prop box box t u) ---> u

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

| red_cast_1 i A B t A' :
    A ---> A' ->
    cast i A B box t ---> cast i A' B box t

| red_cast_2 i A B t B' :
    B ---> B' ->
    cast i A B box t ---> cast i A B' box t

| red_cast_3 i A B t t' :
    t ---> t' ->
    cast i A B box t ---> cast i A B box t'

| red_J_refl l i A a P p :
    Nf a ->
    J l i A a P p a box ---> p

| red_Lift A A' i :
    A ---> A' ->
    Lift i A ---> Lift i A'

| red_lift a a' :
    a ---> a' ->
    lift prop box a ---> lift prop box a'

| red_lower a a' :
    a ---> a' ->
    lower prop box a ---> lower prop box a'

| red_lift_lower a :
    lift prop box (lower prop box a) ---> a

| red_lower_lift a :
    lower prop box (lift prop box a) ---> a

| red_cast_nat t :
    cast (ty 0) Nat Nat box t ---> t

| red_cast_univ i A :
    cast (Ax i) (Sort i) (Sort i) box A ---> A

| red_cast_pi i n A1 B1 A2 B2 f :
    let A1' := S ⋅ A1 in
    let A2' := S ⋅ A2 in
    let t1 := match i with | ty _ => cast i A2' A1' box (var 0) | prop => box end in
    let t2 := app prop prop box box (S ⋅ f) t1 in
    let t3 := cast (ty n) (B1 <[t1.: S >> var]) B2 box t2 in
    let t4 := lam prop prop box box t3 in
    cast (Ru i (ty n)) (Pi i (ty n) A1 B1) (Pi i (ty n) A2 B2) box f ---> t4

| red_sum_1 i j A A' B :
    A ---> A' ->
    tysum i j A B ---> tysum i j A' B

| red_sum_2 i j A B B' :
    B ---> B' ->
    tysum i j A B ---> tysum i j A B'

| red_inl a a' :
    a ---> a' ->
    inl prop prop box box a ---> inl prop prop box box a'

| red_inr b b' :
    b ---> b' ->
    inr prop prop box box b ---> inr prop prop box box b'

| red_sum_case_P l P P' pl pr u :
    P ---> P' →
    sum_case prop prop l box box P pl pr u ---> sum_case prop prop l box box P' pl pr u

| red_sum_case_pl l P pl pl' pr u :
    pl ---> pl' →
    sum_case prop prop l box box P pl pr u ---> sum_case prop prop l box box P pl' pr u

| red_sum_case_pr l P pl pr pr' u :
    pr ---> pr' →
    sum_case prop prop l box box P pl pr u ---> sum_case prop prop l box box P pl pr' u

| red_sum_case_u l P pl pr u u' :
    u ---> u' →
    sum_case prop prop l box box P pl pr u ---> sum_case prop prop l box box P pl pr u'

| red_sum_case_inl l P pl pr a :
    sum_case prop prop l box box P pl pr (inl prop prop box box a) ---> pl <[ a .. ]

| red_sum_case_inr l P pl pr b :
    sum_case prop prop l box box P pl pr (inr prop prop box box b) ---> pr <[ b .. ]

where "t ---> u" := (red t u).

Derive Signature for red.

Lemma case_lvl l : l = prop ∨ exists i, l = ty i.
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

Lemma refines_cons' f g l :
  refines f g -> refines (f ;; l) (g ;; l).
Proof.
  intro ref.
  unfold refines.
  intros.
  destruct x.
  - simpl in H. eexists.  eauto.
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

Lemma erasure_subst_up Δ σ t l :
  (erasure l t) <[ up_term (erasure_subst Δ σ)] =
  (erasure l t) <[ erasure_subst (Δ ;; ty 0) (var 0 .: σ >> ren_term S)].
Proof.
  setoid_rewrite erasure_subst_cons.
  reflexivity.
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

  (* solves all cases not involving binders *)
  all:try solve [ subst;f_equal;eauto ].

  (* case var *)
  - unfold erasure_subst. unfold refines in ref.
    eapply varty_fun_of_ctx in var_in_ctx.
    eapply ref in var_in_ctx as (j & eq).
    rewrite eq.
    apply erasure_irrel.
  (* case pi *)
  - f_equal. eauto using IHt1.  ssimpl.
    transitivity ((erasure (Ax l0) t2) <[ (erasure (ty 0) (var 0)) .: erasure_subst Δ σ >> ren_term ↑]); eauto.
    setoid_rewrite <- erasure_subst_cons.
    eapply IHt2; eauto.
    setoid_rewrite cons_ctx_commute.
    eauto using refines_cons.
  (* case lam *)
  - f_equal. ssimpl.
    transitivity  ((erasure l0 t3) <[ erasure (ty 0) (var 0) .: erasure_subst Δ σ >> ren_term ↑]).
    2 : eauto.
    setoid_rewrite <- erasure_subst_cons.
    eapply IHt3; eauto. setoid_rewrite cons_ctx_commute. eauto using refines_cons.
  (* case sigma *)
  - subst. f_equal. eauto using IHt1.  ssimpl.
    transitivity ((erasure (Ax (ty m)) t2) <[ (erasure (ty 0) (var 0)) .: erasure_subst Δ σ >> ren_term ↑]); eauto.
    setoid_rewrite <- erasure_subst_cons.
    eapply IHt2; eauto.
    setoid_rewrite cons_ctx_commute.
    eauto using refines_cons.
  (* case rec *)
  - f_equal; ssimpl; eauto.
    + transitivity ((erasure (Ax l) t1) <[ erasure (ty 0) (var 0) .: erasure_subst Δ σ >> ren_term ↑]).
      2:eauto.
      setoid_rewrite <- erasure_subst_cons.
      eapply IHt1; eauto. setoid_rewrite cons_ctx_commute. eauto using refines_cons.
    + transitivity ((erasure l t3) <[ erasure (ty 0) (var 0) .: (erasure (ty 0) (var 1) .: erasure_subst Δ σ >> ren_term (↑ >> ↑))]).
      2: eauto.
      setoid_rewrite <- erasure_subst_cons2.
      eapply IHt3; eauto. setoid_rewrite cons_ctx_commute. setoid_rewrite cons_ctx_commute. eauto using refines_cons.
  (* case J *)
  - subst. simpl. f_equal; eauto.
    transitivity ((erasure (Ax (ty n)) t3) <[ erasure (ty 0) (var 0) .: erasure_subst Δ σ >> ren_term ↑]).
    2:eauto.
    setoid_rewrite <- erasure_subst_cons.
    eapply IHt3; eauto using refines_cons. setoid_rewrite cons_ctx_commute. eauto using refines_cons.
  (* case sum *)
  - subst. cbn. f_equal. all: eauto.
    + rewrite erasure_subst_up. eapply IHt3. all: eauto using refines_cons.
      setoid_rewrite cons_ctx_commute. eauto using refines_cons.
    + rewrite erasure_subst_up. eapply IHt4. all: eauto using refines_cons.
      setoid_rewrite cons_ctx_commute. eauto using refines_cons.
    + rewrite erasure_subst_up. eapply IHt5. all: eauto using refines_cons.
      setoid_rewrite cons_ctx_commute. eauto using refines_cons.
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


Definition can t T :=
  match T , t with
  | Pi _ _ _ _, lam _ _ _ _ _
  | Sigma _ _ _ _, pair _ _ _ _ _ _
  | Nat, zero
  | Nat, succ _
  | Lift _ _, lift _ _ _
  | tysum _ _ _ _, inl _ _ _ _ _
  | tysum _ _ _ _, inr _ _ _ _ _
  | Sort _, Pi _ _ _ _
  | Sort _, Sigma _ _ _ _
  | Sort _, Sort _
  | Sort _, Nat
  | Sort _, Lift _ _
  | Sort _, Eq _ _ _ _
  | Sort _, tysum _ _ _ _ => True
  | _, _ => False
end.


Hint Unfold is_type_former : core.

Derive Signature for Nf.

Lemma nf_is_ne Γ l T t :
  Γ ⊢< ty l > t : T ->
  is_type_former T ->
  Nf (erasure (ty l) t) ->
  not (can t T) ->
  Ne (erasure (ty l) t).
Proof.
  intros t_Wt is_tf nf_et t_neq.
  dependent destruction nf_et.

  (* solves Ne case *)
  all:try solve [eauto].

  (* solves box case *)
  all:try solve [ destruct t; dependent destruction H;
    eapply type_inv in t_Wt;dependent destruction t_Wt;
    dependent destruction lvl_eq ].

  (* solves remaining cases *)
  all:try solve [ destruct t; dependent destruction H;
  destruct T; dependent destruction is_tf;
  eapply type_inv in t_Wt as temp; dependent destruction temp;
  lazymatch goal with
  | conv_ty : _ ⊢< _ > _ ≡ _ : Sort _ |- _ =>
    eapply type_formers_inj in conv_ty
  end ;
  unfold can in *; intuition eauto].
Qed.


Definition nf t := forall u, t ---> u -> False.


Hint Unfold ConversionChecking.nf : core.

Scheme Equality for level.
Scheme Equality for term.


Lemma nf_to_Nf Γ l t A :
  Γ ⊢< l > t : A -> nf (erasure l t) -> Nf (erasure l t).
Proof.
  generalize Γ l A. clear Γ l A. induction t; intros Γ l' A t_Wt is_nf.

  all:destruct l'; [idtac | rewrite erasure_prop; eapply nf_box].

  (* solves case box and symbols that can only be in sprop *)
  all:try solve [eapply type_inv in t_Wt; dependent destruction t_Wt; dependent destruction lvl_eq].

  (* solves all constructor cases *)
  all: try solve [ eapply type_inv in t_Wt; dependent destruction t_Wt; ty_inj_tac ; subst ; eauto 24 using Nf, Ne, red].

  (* solves almost all elimination cases *)
  all: try solve [
    eapply type_inv in t_Wt; dependent destruction t_Wt;
    ty_inj_tac; subst;
    eapply nf_ne; simpl;
    econstructor; eauto using red;
    eapply nf_is_ne; eauto using red;
    match goal with
    | |-  ¬ (can ?t _) => destruct t
    end; intro K; inversion K;
    eapply is_nf; simpl; eauto using red ].

  (* case J *)
  - destruct (term_eq_dec (erasure l t2) (erasure l t5)).
    + exfalso.
      eapply type_inv in t_Wt; dependent destruction t_Wt. subst.
      eapply is_nf. cbn. rewrite e. 
      eapply red_J_refl. eapply IHt5; eauto. intro. intro.
      eapply is_nf. eauto using red.
    + eapply type_inv in t_Wt; dependent destruction t_Wt. subst.
      econstructor. cbn. econstructor; eauto using red.
  
  (* case cast *)
  - rename A into T. rename t1 into A. rename t2 into B.
    rename t3 into e. rename t4 into a.
    subst. eapply nf_ne.
    eapply type_inv in t_Wt. dependent destruction t_Wt. subst.
    eassert (Nf (erasure _ A)) as Nf_A by eauto using red.
    eassert (Nf (erasure _ B)) as Nf_B by eauto using red.
    eassert (Nf (erasure _ a)) as Nf_a by eauto using red.
    clear IHt1 IHt2 IHt3 IHt4.

    destruct A; destruct B; eauto using Ne.
    2-27:destruct l0; eauto using Ne.
    + eapply type_inv in A_Wt. dependent destruction A_Wt.
      eapply Ax_inj in lvl_eq. rewrite lvl_eq in *. clear lvl_eq n.
      pose (K := level_eq_dec l l0). destruct K.
      * subst. exfalso. eapply is_nf; simpl; eauto using red.
      * eapply ne_cast3; eauto.
    + eapply type_inv in A_Wt. dependent destruction A_Wt.
      eapply Ax_inj in lvl_eq. rewrite lvl_eq in *. clear lvl_eq n.
      destruct l2. 2:simpl;eauto using Ne.
      clear A_Wt B_Wt conv_ty.
      pose (K := level_eq_dec l l1). pose (K' := level_eq_dec (ty n) (ty n0)).
      destruct K; destruct K'.
      * ty_inj_tac. subst. exfalso. eapply is_nf; simpl; eauto using red.
      * subst. simpl. eapply ne_cast3; intuition eauto.
      * ty_inj_tac. subst. eapply ne_cast3; intuition eauto. fold erasure in *. simpl in H. intuition eauto.
      * simpl. eapply ne_cast3; intuition eauto.
    + eapply type_inv in A_Wt. dependent destruction A_Wt. dependent destruction lvl_eq.
      exfalso. eapply is_nf; eauto using red.
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
    ∧
  (forall et, Ne et ->
    forall Γ i i' t0 u0 T T'
    (t0_Wt : Γ ⊢< ty i > t0 : T)
    (u0_Wt : Γ ⊢< ty i' > u0 : T')
    (erased_t0_eq_erased_u0 : erasure (ty i) t0 = erasure (ty i') u0)
    (et_eq_erased_t0 : et = erasure (ty i) t0),
    Γ ⊢< ty i > t0 ≡ u0 : T).
Proof.
  apply Nf_Ne_mutind; intros.

  (* case Ne t -> Nf t, easy *)
  9: solve [eauto].

  all:(destruct t0; dependent destruction et_eq_erased_t0;
    destruct u0; dependent destruction erased_t0_eq_erased_u0;
    eapply type_inv in t0_Wt as temp; dependent destruction temp;
    eapply type_inv in u0_Wt as temp; dependent destruction temp; subst).

  (* solves cases in sprop *)
  all: try solve [dependent destruction lvl_eq].

  (* solves cases Nat, zero, Sort, var *)
  all: try solve [ eauto using conv_refl ].

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
    apply type_formers_inj in pi_eq_pi as (l_eq_l1 & l0_eq_l2 & A_eq & B_eq); eauto.
    subst. apply conv_lam; eauto.
    destruct l2. 2:inversion lvl_eq.
    eauto 6 using conv_ty_in_ctx_ty, conv_sym, type_conv, conv_ty_in_ctx_conv.
  - ty_inj_tac. subst. rewrite lvl_eq0.
    eapply conv_conv; eauto 6 using conv_sym, conv_sigma, conv_ty_in_ctx_ty.
  - rename t0_1 into A. rename t0_2 into B. rename t0_3 into t. rename t0_4 into u.
    rename u0_1 into A'. rename u0_2 into B'. rename u0_3 into t'. rename u0_4 into u'.
    rewrite lvl_eq. eapply conv_conv; eauto using conv_sym.
    rewrite <- lvl_eq in conv_ty. rewrite <- lvl_eq0 in conv_ty0.
    eassert (_ ⊢< _ > Sigma _ _ A B ≡ Sigma _ _ A' B' : _) as sigma_eq_sigma
      by eauto using conv_sym, conv_trans.
    apply type_formers_inj in sigma_eq_sigma as (l_eq_l1 & l0_eq_l2 & A_eq & B_eq); eauto.
    ty_inj_tac. subst.
    assert (Γ ⊢< ty n2 > t ≡ t' : A)
      by eauto 9 using conv_ty_in_ctx_ty, conv_sym, type_conv, conv_ty_in_ctx_conv, subst_conv, substs_one, type_conv.
    econstructor; eauto 7 using type_conv, subst_conv, validity_ty_ctx, substs_one, conv_sym.
  - dependent destruction lvl_eq.
    eapply conv_conv. 2: eauto using conv_sym.
    apply conv_succ. eauto.
  - dependent destruction lvl_eq.
    eapply conv_conv; eauto using conv_sym.
    eapply conv_Eq; eauto using conv_conv, conv_sym, type_conv.
  - dependent destruction lvl_eq. cbn in *.
    eapply conv_conv; eauto using conv_sym.
    eapply conv_Lift; eauto using conv_conv, conv_sym, type_conv.
  - rename t0_1 into A. rename u0_1 into A'.
    rename t0_2 into a. rename u0_2 into a'.
    rewrite lvl_eq in lvl_eq0. eapply Ax_inj in lvl_eq0. subst.
    assert (_ ⊢< _ > Lift _ A ≡ Lift l0 A' : _) as lift_eq_lift by eauto using conv_sym, conv_trans.
    eapply type_formers_inj in lift_eq_lift as (_ & A_equiv_A'); eauto.
    dependent destruction lvl_eq.
    eapply conv_conv.
    eapply conv_lift; eauto using type_conv, conv_sym.
    eauto using conv_sym.
  - rewrite H6.
    eapply conv_conv. all: eauto 7 using conv_sym, conv_sum, conv_ty_in_ctx_ty.
  - rename t0_1 into A, t0_2 into B, t0_3 into a, u0_1 into A', u0_2 into B', u0_3 into a'.
    rewrite H5. eapply conv_conv; eauto using conv_sym.
    rewrite <- H5 in H4. rewrite <- H10 in H9.
    eassert (_ ⊢< _ > tysum _ _ A B ≡ tysum _ _ A' B' : _) as hsum
      by eauto using conv_sym, conv_trans.
    apply type_formers_inj in hsum as (l_eq_l1 & l0_eq_l2 & A_eq & B_eq); eauto.
    ty_inj_tac. subst.
    assert (Γ ⊢< ty i1 > a ≡ a' : A)
      by eauto 9 using conv_ty_in_ctx_ty, conv_sym, type_conv, conv_ty_in_ctx_conv, subst_conv, substs_one, type_conv.
    econstructor; eauto 7 using type_conv, subst_conv, validity_ty_ctx, substs_one, conv_sym.
  - rename t0_1 into A, t0_2 into B, t0_3 into b, u0_1 into A', u0_2 into B', u0_3 into b'.
    rewrite H5. eapply conv_conv; eauto using conv_sym.
    rewrite <- H5 in H4. rewrite <- H10 in H9.
    eassert (_ ⊢< _ > tysum _ _ A B ≡ tysum _ _ A' B' : _) as hsum
      by eauto using conv_sym, conv_trans.
    apply type_formers_inj in hsum as (l_eq_l1 & l0_eq_l2 & A_eq & B_eq); eauto.
    ty_inj_tac. subst.
    assert (Γ ⊢< ty j0 > b ≡ b' : B)
      by eauto 9 using conv_ty_in_ctx_ty, conv_sym, type_conv, conv_ty_in_ctx_conv, subst_conv, substs_one, type_conv.
    econstructor; eauto 7 using type_conv, subst_conv, validity_ty_ctx, substs_one, conv_sym.
  - rename t0_1 into A. rename t0_2 into B. rename t0_3 into t. rename t0_4 into u.
    rename u0_1 into A'. rename u0_2 into B'. rename u0_3 into t'. rename u0_4 into u'.
    eapply conv_conv; eauto using conv_sym.
    assert (Γ ⊢< Ru l (ty i) > t ≡ t' : Pi l (ty i) A B) as t1_eq_t2 by eauto.
    eapply validity_conv_right, type_unique in t1_eq_t2 as pi_eq_pi. 2:exact t_Wt0.
    eapply type_formers_inj in pi_eq_pi as (eq1 & eq2 & A_eq & B_eq); eauto.
    ty_inj_tac. subst.
    eapply conv_app; eauto using type_conv, conv_sym, conv_ty_in_ctx_conv.
  - rename t0_1 into A. rename t0_2 into B. rename t0_3 into t.
    rename u0_1 into A'. rename u0_2 into B'. rename u0_3 into t'.
    ty_inj_tac. subst.
    eapply conv_conv; eauto using conv_sym.
    eassert (Γ ⊢< _ > t ≡ t' : Sigma _ _ A B) as t1_eq_t2 by eauto.
    eapply validity_conv_right, type_unique in t1_eq_t2 as temp. 2:exact t_Wt0.
    eapply type_formers_inj in temp as (eq1 & eq2 & A_eq & B_eq); eauto.
    ty_inj_tac. subst.
    econstructor; eauto using type_conv, conv_sym, conv_ty_in_ctx_conv.
  - rename t0_1 into A. rename t0_2 into B. rename t0_3 into t.
    rename u0_1 into A'. rename u0_2 into B'. rename u0_3 into t'.
    ty_inj_tac. subst.
    eapply conv_conv; eauto using conv_sym.
    eassert (Γ ⊢< _ > t ≡ t' : Sigma _ _ A B) as t1_eq_t2 by eauto.
    eapply validity_conv_right, type_unique in t1_eq_t2 as temp. 2:exact t_Wt0.
    eapply type_formers_inj in temp as (eq1 & eq2 & A_eq & B_eq); eauto.
    ty_inj_tac. subst.
    econstructor; eauto using type_conv, conv_sym, conv_ty_in_ctx_conv.
  - ty_inj_tac. subst.
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
  - rename t0_1 into A. rename u0_1 into A'.
    rename t0_2 into a. rename u0_2 into a'.
    eapply H in H0 as a'_conv_a; eauto.
    eapply validity_conv_right, type_unique in a'_conv_a as temp. 2:exact a_Wt.
    eapply type_formers_inj in temp as (i_eq_i' & A_conv_A'); eauto.
    ty_inj_tac. subst.
    eapply conv_conv.
    eapply conv_lower; eauto.
    eauto using conv_sym.

  (* the following three cases for cast are basically the same *)
  - rename t0_1 into A. rename t0_2 into B. rename t0_3 into e. rename t0_4 into a.
    rename u0_1 into A'. rename u0_2 into B'. rename u0_3 into e'. rename u0_4 into a'.
    eapply H in H2 as A'_conv_A; eauto. clear H.
    eapply H0' in H3 as B'_conv_B; eauto. clear H0'.
    eapply H1' in H4 as a'_conv_a; eauto using type_conv, conv_sym. clear H1'.
    eapply conv_sym, conv_conv.
    econstructor; eauto 8 using conv_sym, conv_irrel, type_conv, conv_Eq, conv_sort, validity_ty_ctx.
    eauto using conv_sym, conv_trans.
  - rename t0_1 into A. rename t0_2 into B. rename t0_3 into e. rename t0_4 into a.
    rename u0_1 into A'. rename u0_2 into B'. rename u0_3 into e'. rename u0_4 into a'.
    eapply H' in H2 as A'_conv_A; eauto. clear H'.
    eapply H0 in H3 as B'_conv_B; eauto. clear H0.
    eapply H1' in H4 as a'_conv_a; eauto using type_conv, conv_sym. clear H1'.
    eapply conv_sym, conv_conv.
    econstructor; eauto 8 using conv_sym, conv_irrel, type_conv, conv_Eq, conv_sort, validity_ty_ctx.
    eauto using conv_sym, conv_trans.
  - rename t0_1 into A. rename t0_2 into B. rename t0_3 into e. rename t0_4 into a.
    rename u0_1 into A'. rename u0_2 into B'. rename u0_3 into e'. rename u0_4 into a'.
    eapply H' in H2 as A'_conv_A; eauto. clear H'.
    eapply H0' in H3 as B'_conv_B; eauto. clear H0'.
    eapply H1' in H4 as a'_conv_a; eauto using type_conv, conv_sym. clear H1'.
    eapply conv_sym, conv_conv.
    econstructor; eauto 8 using conv_sym, conv_irrel, type_conv, conv_Eq, conv_sort, validity_ty_ctx.
    eauto using conv_sym, conv_trans.

  - rename t0_1 into A, t0_2 into B, t0_3 into P, t0_4 into pl, t0_5 into pr, t0_6 into u.
    rename u0_1 into A', u0_2 into B', u0_3 into P', u0_4 into pl', u0_5 into pr', u0_6 into u'.
    eapply H2 in H6 as Hu. all: eauto.
    eapply type_unique in H12 as he.
    2:{ eapply validity_conv_right in Hu. eapply Hu. }
    apply type_formers_inj in he as hh.
    destruct hh as (l_eq_l1 & l0_eq_l2 & A_eq & B_eq); eauto.
    ty_inj_tac. subst.
    eapply H' in H3 as HP. all: eauto.
    2: eauto using conv_ty_in_ctx_ty, conv_sym.
    eapply H0' in H4 as Hpl. all: eauto.
    2:{
      eapply conv_ty_in_ctx_ty. 1: econstructor.
      - eauto.
      - eapply subst_conv.
        all: eauto 7 using type_conv, subst_conv, validity_ty_ctx, substs_one, conv_sym.
        apply conv_scons_alt.
        1: eauto using refl_subst, ortho_to_conv, validity_conv_right with sidecond.
        rasimpl. econstructor.
        { econstructor.
          all: eauto using conv_sym, conv_ren, ortho_to_conv, validity_conv_right with sidecond.
          apply conv_refl.
          eauto using typing, ortho_to_conv, validity_conv_right with sidecond.
        }
        eapply conv_ren in he. 3: eapply WellRen_S.
        all: eauto using conv_sym, validity_ty_ctx.
      - eauto using conv_sym.
    }
    eapply H1' in H5 as Hpr. all: eauto.
    2:{
      eapply conv_ty_in_ctx_ty. 1: econstructor.
      - eauto.
      - eapply subst_conv.
        all: eauto 7 using type_conv, subst_conv, validity_ty_ctx, substs_one, conv_sym.
        apply conv_scons_alt.
        1: eauto using refl_subst, ortho_to_conv, validity_conv_right with sidecond.
        rasimpl. econstructor.
        { econstructor.
          all: eauto using conv_sym, conv_ren, ortho_to_conv, validity_conv_right with sidecond.
          apply conv_refl.
          eauto using typing, ortho_to_conv, validity_conv_right with sidecond.
        }
        eapply conv_ren in he. 3: eapply WellRen_S.
        all: eauto using conv_sym, validity_ty_ctx.
      - eauto using conv_sym.
    }
    eapply conv_sym. eapply conv_conv.
    { econstructor.
      all: eauto 7 using type_conv, subst_conv, validity_ty_ctx, substs_one, conv_sym.
    }
    eauto 7 using conv_trans, type_conv, subst_conv, validity_ty_ctx, substs_one, conv_sym.
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
  exists u', Γ ⊢< l > t ≡ u' : A ∧ erasure l u' = u.
Proof.
  intros t_Wt et_red.
  remember (erasure l t) as lhs.
  generalize Γ l t A t_Wt Heqlhs. clear Heqlhs  Γ l t A t_Wt Heqlhs.
  induction et_red; intros Γ l0 t0 A0 t0_Wt eq.


  (* the case l = prop is impossible, and in the case l = ty _
    erasure l t0 computes so we can destruct t0 and
    by inversion on the equality we know it has the right shape *)
  all:destruct l0; [ destruct t0; dependent destruction eq |
    rewrite erasure_prop in eq; dependent destruction eq ].

  (* solves all cases of a rewrite not at the root *)
  all:try solve [
    eapply type_inv in t0_Wt; dependent destruction t0_Wt;
    ty_inj_tac; subst;
    eassert (_ = _) as temp by reflexivity;
    eapply IHet_red in temp as (u0 & conv & erased_u0); eauto;
    subst;
    eexists; split; [
      rewrite ?lvl_eq in * ;
      eapply conv_conv ; [
        econstructor; eauto 6 using conv_refl
      | eauto using conv_sym
      ]
    | reflexivity
    ]
  ].

  (* we do type inversion in all cases *)
  all: eapply type_inv in t0_Wt; dependent destruction t0_Wt; ty_inj_tac;subst.

  (* case pi1pair *)
  - destruct t0_3; dependent destruction H.
    rename l into i'. rename l0 into j'. rename t0_3_1 into A'.
    rename t0_3_2 into B. rename t0_3_3 into u. rename t0_3_4 into v.
    eapply type_inv in t_Wt as temp; dependent destruction temp.
    eapply type_formers_inj in conv_ty0 as (eq1 & eq2 & A_conv_A' & B_conv_B'); eauto. ty_inj_tac. subst.
    eexists. split.
    * eapply conv_conv.
      eapply conv_pi1pair' ; eauto 7 using type_conv, conv_sym, subst_conv, substs_one, validity_ty_ctx, conv_refl.
      eapply type_conv; eauto. eapply subst_conv; eauto 9 using conv_sym, substs_one, validity_ty_ctx.
      eapply substs_one;eauto using type_conv, conv_refl, conv_sym.
      eauto using conv_sym.
    * reflexivity.

  (* case pi2pair *)
  - destruct t0_3; dependent destruction H.
    rename l into i'. rename l0 into j'. rename t0_3_1 into A'.
    rename t0_3_2 into B. rename t0_3_3 into u. rename t0_3_4 into v.
    eapply type_inv in t_Wt as temp; dependent destruction temp.
    eapply type_formers_inj in conv_ty0 as (eq1 & eq2 & A_conv_A' & B_conv_B'); eauto. ty_inj_tac. subst.
    eexists. split.
    * eapply conv_conv.
      ** eapply conv_pi2pair'; eauto 7 using type_conv, conv_sym, subst_conv, substs_one, validity_ty_ctx, conv_refl.
         eapply type_conv; eauto. eapply subst_conv; eauto 9 using conv_sym, substs_one, validity_ty_ctx.
         eapply substs_one;eauto using type_conv, conv_refl, conv_sym.
      ** eapply conv_trans.
         2:eauto using conv_sym.
         eapply subst_conv; eauto using conv_refl, validity_ty_ctx.
         eapply substs_one, conv_sym.
         eapply conv_pi1pair'; eauto 7 using type_conv, conv_sym, subst_conv, substs_one, validity_ty_ctx, conv_refl.
      eapply type_conv; eauto. eapply subst_conv; eauto 9 using conv_sym, substs_one, validity_ty_ctx.
      eapply substs_one;eauto using type_conv, conv_refl, conv_sym.
    * reflexivity.

  (* case beta *)
  - destruct t0_3; dependent destruction H.
    rename l into i'. rename l0 into j'. rename t0_3_1 into A'.
    rename t0_3_2 into B. rename t0_3_3 into u.
    eapply type_inv in t_Wt as temp; dependent destruction temp.
    eapply type_formers_inj in conv_ty0 as (eq1 & eq2 & A_conv_A' & B_conv_B'); eauto. ty_inj_tac. subst.
    eexists. split.
    * eauto using conv_conv, conv_beta', conv_sym.
    * eapply erasure_subst_1_commutes; eauto.

  (* case rec zero *)
  - destruct t0_4; dependent destruction H.
    eexists. split; eauto using conv_rec_zero, conv_conv, conv_sym.

  (* case rec succ *)
  - destruct t0_4; dependent destruction H.
    eapply type_inv in t_Wt; dependent destruction t_Wt.
    eexists. split.
    * eauto using conv_rec_succ, conv_conv, conv_sym.
    * erewrite erasure_subst_2_commutes; eauto. reflexivity.

  (* case J_refl *)
  - eexists. split.
    eapply conv_conv.
    eapply conv_J_refl'; eauto.
    + destruct l. 2:eauto using conv_irrel.
      eapply (proj1 eq_erased) in H; eauto.
    + eauto using conv_sym.
    + reflexivity.

  (* case lift_lower *)
  - destruct l. 2: rewrite erasure_prop in H; inversion H.
    destruct t0_2; dependent destruction H.
    eapply type_inv in a_Wt as temp. dependent destruction temp. subst. rewrite lvl_eq in *.
    eexists. split.
    + eauto 7 using conv_conv, conv_sym, conv_lift_lower', conv_Lift, type_conv.
    + reflexivity.

  (* case lower_lift *)
  - destruct t0_2; dependent destruction H.
    eapply type_inv in a_Wt as temp. dependent destruction temp.
    eapply type_formers_inj in conv_ty0 as (_ & A_conv_a1); eauto.
    eapply Ax_inj in lvl_eq. subst.
    eexists. split.
    + eauto 7 using conv_conv, conv_lower_lift', type_conv, conv_sym.
    + reflexivity.

  (* case cast_nat *)
  - destruct t0_1; dependent destruction H.
    destruct t0_2; dependent destruction H0.
    eexists; eauto using conversion.

  (* case cast_univ *)
  - destruct t0_1; dependent destruction H.
    destruct t0_2; dependent destruction H0.
    rewrite lvl_eq in *.
    eexists; eauto using conversion.

  (* case cast_pi *)
  - destruct t0_1; dependent destruction H.
    destruct t0_2; dependent destruction H0.
    unfold_all_local.
    eapply type_inv in A_Wt. dependent destruction A_Wt.
    eapply type_inv in B_Wt. dependent destruction B_Wt.
    eexists. split.
    + eauto using conv_conv, conv_sym,  conv_cast_pi.
    + simpl. f_equal. rasimpl. f_equal.
      * erewrite erasure_subst_commutes; eauto.
        2:{ setoid_rewrite cons_ctx_commute.
            eapply refines_cons'; eauto. eapply refines_all. }
        eapply subst_term_morphism; eauto.
        unfold pointwise_relation. intros a0; destruct a0; unfold erasure_subst; simpl.
        ++ rewrite erasure_rename_commute. rewrite erasure_rename_commute. destruct i; reflexivity.
        ++  reflexivity.
      * rasimpl. rewrite erasure_rename_commute. rewrite erasure_rename_commute. rewrite erasure_rename_commute.
        f_equal. destruct i; reflexivity.

  (* No longer solved by automation :( *)
  - ty_inj_tac ; subst ;
    eassert (_ = _) as temp by reflexivity;
    eapply IHet_red in temp as (u0 & conv & erased_u0); eauto;
    subst.
    eexists; split.
    + match goal with
      | lvl_eq : _ = _ :> level |- _ => rewrite ?lvl_eq in *
      end.
      eapply conv_conv.
      * econstructor; eauto 6 using conv_refl.
      * eauto using conv_sym.
    + reflexivity.

  - ty_inj_tac ; subst ;
    eassert (_ = _) as temp by reflexivity;
    eapply IHet_red in temp as (u0 & conv & erased_u0); eauto;
    subst.
    eexists; split.
    + match goal with
      | lvl_eq : _ = _ :> level |- _ => rewrite ?lvl_eq in *
      end.
      eapply conv_conv.
      * econstructor; eauto 6 using conv_refl.
      * eauto using conv_sym.
    + reflexivity.

  (* sum_case_inl *)
  - destruct t0_6. all: noconf H.
    eapply type_inv in H5. dependent destruction H5.
    eapply type_formers_inj in H8 as he. 2,3: eauto.
    destruct he as (l_eq_l1 & l0_eq_l2 & A_eq & B_eq); eauto.
    ty_inj_tac. subst.
    eexists. split.
    + eapply conv_conv.
      { eapply conv_sum_case_inl'.
        all: eauto.
        eauto using type_conv, conv_sym.
      }
      eapply conv_trans. 2: eauto using conv_sym.
      eapply subst_conv. all: eauto using validity_ty_ctx, conv_refl.
      apply substs_one.
      apply conv_inl. all: eauto using conv_refl, conv_sym, type_conv.
    + erewrite erasure_subst_commutes. all: eauto.
      2:{
        setoid_rewrite cons_ctx_commute.
        eapply refines_cons'; eauto. eapply refines_all.
      }
      apply ext_term. intros []. all: reflexivity.

  (* sum_case_inr *)
  - destruct t0_6. all: noconf H.
    eapply type_inv in H5. dependent destruction H5.
    eapply type_formers_inj in H8 as he. 2,3: eauto.
    destruct he as (l_eq_l1 & l0_eq_l2 & A_eq & B_eq); eauto.
    ty_inj_tac. subst.
    eexists. split.
    + eapply conv_conv.
      { eapply conv_sum_case_inr'.
        all: eauto.
        eauto using type_conv, conv_sym.
      }
      eapply conv_trans. 2: eauto using conv_sym.
      eapply subst_conv. all: eauto using validity_ty_ctx, conv_refl.
      apply substs_one.
      apply conv_inr. all: eauto using conv_refl, conv_sym, type_conv.
    + erewrite erasure_subst_commutes. all: eauto.
      2:{
        setoid_rewrite cons_ctx_commute.
        eapply refines_cons'; eauto. eapply refines_all.
      }
      apply ext_term. intros []. all: reflexivity.
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
  exists u, Γ ⊢< l > t ≡ u : A ∧ erasure l u = u'.
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
  exists u', Γ ⊢< l > t ≡ u' : A ∧ erasure l u' = u.
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

Hint Unfold nf : core.


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

  assert (exists X, fst X = l ∧ snd X = t ) as (X & eq1 & eq2).
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
