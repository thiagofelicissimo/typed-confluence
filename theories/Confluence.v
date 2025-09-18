(** * Typing *)

From Stdlib Require Import Utf8 List Arith Bool Lia.
From TypedConfluence.autosubst
Require Import core unscoped AST SubstNotations RAsimpl AST_rasimpl.
From TypedConfluence Require Import Util BasicAST Weakenings Contexts Typing BasicMetaTheory. (*  Env Inst. *)
From Stdlib Require Import Setoid Morphisms Relation_Definitions.

Reserved Notation "Γ ⊢< l > t ⟹ u : T" (at level 50, l, t, u, T at next level).
Import CombineNotations.

Inductive ortho_red : ctx -> level -> term -> term → term → Prop :=

| ortho_var :
    ∀ Γ x l A,
      ⊢ Γ -> 
      nth_error Γ x = Some (l , A) →
      (Γ ⊢< l > (var x) ⟹ (var x) : ((plus (S x)) ⋅ A))

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
      Γ ⊢< l > p_zero ⟹ p_zero' : P <[ p_zero .. ] -> 
      Γ ,, (ty 0 , Nat) ,, (l , P <[ (var 0) .. ]) ⊢< l > p_succ ⟹ p_succ' : P <[ (succ (var 0)) .. ] ->
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

| ortho_eta : 
    ∀ Γ i j A1 B1 t A2 B2 t',
      Γ ⊢< Ax i > A1 ≡ A2 : Sort i →
      Γ ,, (i , A1) ⊢< Ax j > B1 ≡ B2 : Sort j →
      Γ ⊢< Ru i j > t ⟹ t' : Pi i j A1 B1 →
      let t_wk := wk_tm (_wk_step _wk_id) t in 
      let A2_wk := wk_tm (_wk_step _wk_id) A2 in 
      let B2_wk := wk_tm (_wk_up (_wk_step _wk_id)) B2 in (* is this right? *)
      Γ ⊢< Ru i j > lam i j A1 B1 (app i j A2_wk B2_wk t_wk (var 0)) ⟹ t' : Pi i j A1 B1

| ortho_rec_zero : 
    ∀ Γ l P p_zero p_succ p_zero',
      Γ ,, (ty 0 , Nat) ⊢< Ax l > P : Sort l ->
      Γ ⊢< l > p_zero ⟹ p_zero' : P <[ p_zero .. ] -> 
      Γ ,, (ty 0 , Nat) ,, (l , P <[ (var 0) .. ]) ⊢< l > p_succ : P <[ (succ (var 0)) .. ] ->
      Γ ⊢< l > rec l P p_zero p_succ zero ⟹ p_zero' : P <[ zero .. ]

| ortho_rec_succ : 
    ∀ Γ l P p_zero p_succ t P' p_zero' p_succ' t',
      Γ ,, (ty 0 , Nat) ⊢< Ax l > P ⟹ P' : Sort l ->
      Γ ⊢< l > p_zero ⟹ p_zero' : P <[ p_zero .. ] -> 
      Γ ,, (ty 0 , Nat) ,, (l , P <[ (var 0) .. ]) ⊢< l > p_succ ⟹ p_succ' : P <[ (succ (var 0)) .. ] ->
      Γ ⊢< ty 0 > t ⟹ t' : Nat ->
      Γ ⊢< l > rec l P p_zero p_succ (succ t) ⟹ 
          p_succ' <[ t' .: (rec l P' p_zero' p_succ' t') ..] : P <[ (succ t) .. ]
  

where "Γ ⊢< l > t ⟹ u : A" := (ortho_red Γ l t u A).


Reserved Notation "Γ ⊢s σ ⟹ τ : Δ" (at level 50, σ, τ, Δ at next level).

Inductive ortho_subst (Γ : ctx) : ctx -> (nat -> term) -> (nat -> term) -> Prop :=
  | well_sempty (σ σ' : nat -> term) : 
    Γ ⊢s σ ⟹ σ' : ∙
  | well_scons (σ σ' : nat -> term) (Δ : ctx) l (A : term) :
    Γ ⊢s (↑ >> σ) ⟹ (↑ >> σ') : Δ ->
    Γ ⊢< l > σ var_zero ⟹ σ' var_zero : A <[↑ >> σ] ->
    Γ ⊢s σ ⟹ σ' : (Δ ,, (l , A)) 
where "Γ ⊢s σ ⟹ τ : Δ" := (ortho_subst Γ Δ σ τ).

Theorem ortho_refl : 
  forall Γ l t A, 
    Γ ⊢< l > t : A -> 
    Γ ⊢< l > t ⟹ t : A.
Admitted.

Theorem ortho_to_conv : 
  forall Γ l t u A,
    Γ ⊢< l > t ⟹ u : A -> 
    Γ ⊢< l > t ≡ u : A.
Admitted.

Theorem ortho_validity : 
  forall Γ l t u A,
    Γ ⊢< l > t ⟹ u : A -> 
    (Γ ⊢< l > t : A) /\ (Γ ⊢< l > u : A).
Admitted.

Theorem ortho_wk :
  forall Γ Δ l t u A ρ, 
  ⊢ Δ -> 
  ρ : Γ ⊆ Δ ->
  Γ ⊢< l > t ⟹ u : A -> 
  Δ ⊢< l > (wk_tm ρ t) ⟹ (wk_tm ρ u) : (wk_tm ρ A).
Admitted.

Theorem ortho_conv_in_ctx :
  forall Γ Δ l t u A, 
  ⊢ Γ ≡ Δ -> 
  Γ ⊢< l > t ⟹ u : A -> 
  Δ ⊢< l > t ⟹ u : A.
Admitted.

Theorem ortho_subst_property : 
  forall Γ l t u A Δ σ τ, 
    Δ ⊢s σ ⟹ τ : Γ -> 
    Γ ⊢< l > t ⟹ u : A -> 
    Δ ⊢< l > (t <[ σ ]) ⟹ (u <[ τ ]) : A <[ σ ].
Admitted.

(* the diamond property at sort prop is trivial *)

Theorem ortho_diamond_prop : 
  forall Γ t t' t'' A,
    Γ ⊢< prop > t ⟹ t' : A ->
    Γ ⊢< prop > t ⟹ t'' : A ->
    exists t''', (Γ ⊢< prop > t' ⟹ t''' : A) /\ (Γ ⊢< prop > t'' ⟹ t''' : A).
Proof.
  intros.
  apply ortho_validity in H. destruct H.
  apply ortho_validity in H0. destruct H0.
  exists t.
  split; apply ortho_irrel; auto.
Qed. 


(* Inversion principles for ⟹ *)

Lemma ortho_var_inv Γ i x t A :
  Γ ⊢< ty i > var x ⟹ t : A →
  ∃ B,
    t = var x  ∧
    ⊢ Γ ∧
    nth_error Γ x = Some (ty i, B) ∧
    Γ ⊢< Ax (ty i) > (plus (S x)) ⋅ B ≡ A : Sort (ty i).
Proof.
Admitted.

Lemma ortho_sort_inv Γ l l' t A :
  Γ ⊢< l' > Sort l ⟹ t : A →
  ⊢ Γ ∧
  t = Sort l  ∧ l' = Ax (Ax l)  ∧
  Γ ⊢< Ax (Ax (Ax l)) > Sort (Ax l) ≡ A : Sort (Ax l).
Proof.
Admitted.

Lemma ortho_pi_inv Γ l1 l2 l' t' A B T :
  Γ ⊢< l' > Pi l1 l2 A B ⟹ t' : T →
  exists A' B',
    t' = Pi l1 l2 A' B'  ∧
    l' =  Ax (Ru l1 l2) ∧
    Γ ⊢< Ax l1 > A ⟹ A' : Sort l1 ∧
    Γ ,, (l1 , A) ⊢< Ax l2 > B ⟹ B' : Sort l2 ∧
    Γ ⊢< Ax (Ax (Ru l1 l2)) > Sort (Ru l1 l2) ≡ T : Sort (Ax (Ru l1 l2)).
Proof.
Admitted.

Lemma ortho_lam_inv Γ i l1 l2 A1 B1 t u T :
  Γ ⊢< ty i > lam l1 l2 A1 B1 t ⟹ u : T →
  ty i = Ru l1 l2 ∧ 
  Γ ⊢< Ax (Ru l1 l2) > Pi l1 l2 A1 B1 ≡ T : Sort (Ru l1 l2)  ∧
 (( (* a congruence rule *)
    exists A1' B1' t',
      u = lam l1 l2 A1' B1' t' ∧
      Γ ⊢< Ax l1 > A1 ≡ A1' : Sort l1 ∧
      Γ ,, (l1 , A1) ⊢< Ax l2 > B1 ≡ B1' : Sort l2 ∧
      Γ ,, (l1 , A1) ⊢< l2 > t ⟹ t' : B1
  ) \/ ( (* an application of eta*)
    exists A2 B2 v v',

      let v_wk := wk_tm (_wk_step _wk_id) v in 
      let A2_wk := wk_tm (_wk_step _wk_id) A2 in 
      let B2_wk := wk_tm (_wk_up (_wk_step _wk_id)) B2 in
      t = app l1 l2 A2_wk B2_wk v_wk (var 0)  ∧
      
      Γ ⊢< Ax l1 > A1 ≡ A2 : Sort l1  ∧
      Γ ,, (l1 , A1) ⊢< Ax l2 > B1 ≡ B2 : Sort l2  ∧
      Γ ⊢< Ru l1 l2 > v ⟹ v' : Pi l1 l2 A1 B1  ∧
      u = v'
  )).
Admitted.

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
Admitted.


(* TODO finish *)

Ltac ttinv h :=
  lazymatch type of h with
  _ ⊢< _ > ?t ⟹ _ : _ =>
    lazymatch t with
    | var _ => eapply ortho_var_inv in h
    | Sort _ => eapply ortho_sort_inv in h
    | Pi _ _ _ _ => eapply ortho_pi_inv in h
    | lam _ _ _ _ _ => eapply ortho_lam_inv in h as h'
    | app _ _ _ _ _ _ => eapply ortho_app_inv in h as h'
    | _ => h
    end
  end.



(* allows us to close the diamond with different types in the two ends *)
Lemma ortho_diamond_helper Γ l t t' t'' A :
  Γ ⊢< l > t ⟹ t' : A -> 
  Γ ⊢< l > t ⟹ t'' : A -> 
    (exists B C l' l'' t''', (Γ ⊢< l' > t' ⟹ t''' : B) /\ (Γ ⊢< l'' > t'' ⟹ t''' : C)) ->
    exists t''', (Γ ⊢< l > t' ⟹ t''' : A) /\ (Γ ⊢< l > t'' ⟹ t''' : A).
Proof.
  intros. destruct H1. destruct H1. destruct H1. destruct H1. destruct H1. exists x3. destruct H1.
  destruct (ortho_validity _ _ _ _ _ H). destruct (ortho_validity _ _ _ _ _ H0).
  destruct (ortho_validity _ _ _ _ _ H1). destruct (ortho_validity _ _ _ _ _ H2).
  split.
  - pose (K := type_unicity _ _ _ _ _ _ H7 H4). destruct K. eapply ortho_conv. rewrite <- H11. apply H1. rewrite H11 in H12. apply H12.
  - pose (K := type_unicity _ _ _ _ _ _ H9 H6). destruct K. eapply ortho_conv. rewrite <- H11. apply H2. rewrite H11 in H12. apply H12.
Qed.


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
end.

Theorem size_ren t f : size t = size (ren_term f t).
Proof.
  generalize f.
  induction t; auto; intros; simpl.
  - rewrite (IHt1 f0). rewrite (IHt2 (upRen_term_term f0)). lia.
  - rewrite (IHt1 f0). rewrite (IHt2 (upRen_term_term f0)).  rewrite (IHt3 (upRen_term_term f0)). lia.
  - rewrite (IHt1 f0). rewrite (IHt2 (upRen_term_term f0)).  rewrite (IHt3 f0). rewrite (IHt4 f0). lia.
  - rewrite (IHt f0). lia.
  - rewrite (IHt1 (upRen_term_term f0)). rewrite (IHt2 f0). rewrite (IHt3 (upRen_term_term (upRen_term_term f0))). rewrite (IHt4 f0). lia.
Qed.

Theorem size_wk t ρ : size t = size (wk_tm ρ t).
Proof.
  apply size_ren.
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
  -  apply (H _ H0); auto.
  - apply (ortho_diamond_prop _ _ _ _ _ H1 H2).
Qed.



(* TODO: think of some nice tactics to make the easy cases of the proof more direct *)

Theorem ortho_diamond : 
  forall Γ i t t' t'' T,
    Γ ⊢< ty i > t ⟹ t' : T ->
    Γ ⊢< ty i > t ⟹ t'' : T ->
    exists t''', (Γ ⊢< ty i > t' ⟹ t''' : T) /\ (Γ ⊢< ty i > t'' ⟹ t''' : T).
Proof.
  intros Γ i t. generalize t Γ i. clear Γ i t. 
  
  refine (@well_founded_ind _ (fun t u => size t < size u) _ _ _).
  admit. intros.   

  destruct x; eapply (ortho_diamond_helper _ _ _ _ _ _ H0 H1). 

  (* var *)
  - ttinv H0. ttinv H1.
    destruct H0. destruct H0. rewrite H0. destruct H2. destruct H3. 
    destruct H1. destruct H1. rewrite H1. destruct H5. destruct H6. 
    eexists. eexists. eexists. eexists. exists (var n). split; apply ortho_var; eauto.
  
  (* sort *)
    - ttinv H0. ttinv H1.
    destruct H0. destruct H2. rewrite H2. destruct H3.
    destruct H1. destruct H5. rewrite H5. destruct H6.
    eexists. eexists. eexists. eexists. exists (Sort l). split; apply ortho_sort; eauto.


  (* pi *)
  - ttinv H0. ttinv H1. rename x1 into A. rename x2 into B. 
    destruct H0 as (A' & H0). destruct H0 as (B' & H0). destruct H0. destruct H2. destruct H3. destruct H4. rewrite H0.
    destruct H1 as (A'' & H1). destruct H1 as (B'' & H1). destruct H1. destruct H6.  destruct H7. destruct H8.  rewrite H1.

    pose proof (H' := ortho_diamond_helper2 _ H). clear H.
(* 

    pose (IHt2' := ortho_diamond_helper2 _ IHt2). *)

    epose proof (K1 := H' _ _ _ _ _ _ _ H3 H7). destruct K1 as (A''' & K1). destruct K1. shelve. Unshelve. simpl. lia.

    epose proof (K2 := H' _ _ _ _ _ _ _ H4 H8). destruct K2 as (B''' & K2). destruct K2. shelve. Unshelve. simpl. lia.


    assert (⊢ Γ). { pose (K := ortho_to_conv _ _ _ _ _ H3). apply validity_conv in K. destruct K. apply validity_ty in H13. destruct H13. auto. }

    eexists. eexists. eexists. eexists. exists (Pi l l0 A''' B''').
    split; apply ortho_pi; auto. 
    + refine (ortho_conv_in_ctx _ _ _ _ _ _ _ H11). apply conv_ccons. apply refl_ctx. auto. auto using ortho_to_conv.
    + refine (ortho_conv_in_ctx _ _ _ _ _ _ _ H12). apply conv_ccons. apply refl_ctx. auto. auto using ortho_to_conv.

  (* lam *)
  - admit.

  (* app *)
  - rename x1 into A. rename x2 into B. rename x3 into t. rename x4 into u. 
    ttinv H0. clear H0. destruct h'. destruct H2.
    ttinv H1. clear H1. destruct h'. destruct H4. 

    rename t' into v'. rename t'' into v''.

    destruct H3.
    + destruct H5.
      (* case app-cong x app-cong *)
      ++ admit. 
      (* case app-cong x beta *)
      ++ destruct H3 as (A' & H3). destruct H3 as (B' & H3). destruct H3 as (t' & H3). destruct H3 as (u' & H3). 
        destruct H3.  destruct H6.  destruct H7. destruct H8. 


        rewrite H3. clear H3. clear v'.  

        destruct H5 as (A2 & H5). destruct H5 as (B2 & H5). destruct H5 as (w & H5). destruct H5 as (w'' & H5). 
        destruct H5 as (u'' & H5).  destruct H5.  destruct H5. destruct H10. destruct H11.  destruct H12. 
        
        rewrite H13. clear H13. clear v''. 

        pose proof (H' := ortho_diamond_helper2 _ H). clear H.

        rewrite H3 in *. clear H3. clear t.

        epose proof (K1 := H' _ _ _ _ _ _ _ H9 H12). destruct K1 as (u''' & K1). destruct K1. shelve. Unshelve. simpl. lia. 
        
        rewrite <- H0 in *. clear H0 H1. clear l0.


        assert (⊢ Γ) as H''. { pose (K := ortho_to_conv _ _ _ _ _ H3). apply validity_conv in K. destruct K. apply validity_ty in H0. destruct H0. auto. }

        ttinv H8.
        destruct h'. destruct H1. destruct H13. 
        (* case lam-cong *)
        * destruct H13 as (A2' & H13).  destruct H13 as (B2' & H13). destruct H13 as (w' & H13). 
          destruct H13. destruct H14. destruct H15.  rewrite H13 in *. clear H13. clear t'.
          clear H0.

          assert (Γ,, (l, A) ⊢< ty i > w ⟹ w' : B). 
          {
            eapply ortho_conv_in_ctx in H16. shelve. apply conv_ccons. apply refl_ctx. auto. apply conv_sym. apply H5. 
            Unshelve. apply (ortho_conv _ _ _ _ _ _ H16). apply conv_sym. auto. 
          } 

          epose proof (K1 := H' _ _ _ _ _ _ _ H0 H11). destruct K1 as (w''' & K1). destruct K1. shelve. Unshelve. simpl. lia. 

          eexists. eexists. eexists. eexists.
          exists (w''' <[ u''' ..]).
          split.
          (* closing left side *)
          ** apply ortho_beta. 
            *** eapply conv_trans. apply conv_sym. apply H6. eapply conv_trans. apply H5. apply H14. 
            *** eapply conv_in_ctx_conv. apply conv_ccons. apply refl_ctx. auto. apply H6.
                eapply conv_trans. apply conv_sym. apply H7. eapply conv_trans. apply H10. eapply conv_in_ctx_conv. 
                apply conv_ccons. apply refl_ctx. auto. apply conv_sym. apply H5. auto.
            *** eapply ortho_conv_in_ctx. apply conv_ccons. apply refl_ctx. auto. apply H6. eapply ortho_conv. apply H13. auto. 
            *** eapply ortho_conv. apply H. auto.
          (* closing right side *)
          ** admit.
          (* eapply ortho_subst_property. apply (well_scons _ _ _ (Γ,, (l, A))). shelve. simpl. apply H3.     *)
        (* case eta *)
        * admit.
    
    + destruct H5.
      (* case beta x app-cong *)
      ++ admit.
      (* case beta x beta *)
      ++ admit.
  
  (* Nat *)
  - admit.
  
  (* zero *)
  - admit.

  (* succ *)
  - admit.   
  (* rec *)
  - admit.   

Admitted.

