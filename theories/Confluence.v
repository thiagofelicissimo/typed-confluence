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

(* | ortho_eta : 
    ∀ Γ i j A1 B1 t A2 B2 t',
      Γ ⊢< Ax i > A1 ≡ A2 : Sort i →
      Γ ,, (i , A1) ⊢< Ax j > B1 ≡ B2 : Sort j →
      Γ ⊢< Ru i j > t ⟹ t' : Pi i j A1 B1 →
      let t_wk := wk_tm (_wk_step _wk_id) t in 
      let A2_wk := wk_tm (_wk_step _wk_id) A2 in 
      let B2_wk := wk_tm (_wk_up (_wk_step _wk_id)) B2 in (* is this right? *)
      Γ ⊢< Ru i j > lam i j A1 B1 (app i j A2_wk B2_wk t_wk (var 0)) ⟹ t' : Pi i j A1 B1 *)

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

Theorem ortho_subst_id :
  forall Γ,
  ⊢ Γ ->
  Γ ⊢s var ⟹ var : Γ.
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
  exists A1' B1' t',
    ty i = Ru l1 l2 ∧ 
    Γ ⊢< Ax (Ru l1 l2) > Pi l1 l2 A1 B1 ≡ T : Sort (Ru l1 l2)  ∧
    u = lam l1 l2 A1' B1' t' ∧
    Γ ⊢< Ax l1 > A1 ≡ A1' : Sort l1 ∧
    Γ ,, (l1 , A1) ⊢< Ax l2 > B1 ≡ B1' : Sort l2 ∧
    Γ ,, (l1 , A1) ⊢< l2 > t ⟹ t' : B1.
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

Lemma ortho_nat_inv Γ l' t A :
  Γ ⊢< l' > Nat ⟹ t : A → t = Nat.
Proof.
Admitted.

Lemma ortho_zero_inv Γ l' t A :
  Γ ⊢< l' > zero ⟹ t : A → t = zero.
Proof.
Admitted.

Lemma ortho_succ_inv Γ l' t n A :
  Γ ⊢< l' > succ n ⟹ t : A → 
  exists n',
    t = succ n' /\
    Γ ⊢< ty 0 > n ⟹ n' : Nat.
Proof.
Admitted.




(* TODO finish *)

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

(* 
Lemma ortho_diamond_app_beta : 
  Γ ⊢< _ > A ≡ A' : (Sort l1) -> 
  Γ ,, (l1 , A) ⊢< _ > B ≡ B' : (Sort l2) -> 
  
  Γ ,, (l1 , A) ⊢< _ > u ⟹ u' : B -> 
  Γ ⊢< _ > v ⟹ v' : A ->
  
  Γ ,, (l1 , A') ⊢< _ > u ⟹ u' : B' -> 
  Γ ⊢< _ > v ⟹ v' : A ->
   *)


(* TODO: think of some nice tactics to make the easy cases of the proof more direct *)

Theorem ortho_diamond_ty : 
  forall Γ i t t' t'' T,
    Γ ⊢< ty i > t ⟹ t' : T ->
    Γ ⊢< ty i > t ⟹ t'' : T ->
    exists t''', (Γ ⊢< ty i > t' ⟹ t''' : T) /\ (Γ ⊢< ty i > t'' ⟹ t''' : T).
Proof.
  intros Γ i t. generalize t Γ i. clear Γ i t. 
  
  refine (@well_founded_ind _ (fun t u => size t < size u) _ _ _).
  admit. intros t IH Γ i t' t'' T t_red_t' t_red_t''.

  destruct t; eapply (ortho_diamond_helper _ _ _ _ _ _ t_red_t' t_red_t''); 
  pose proof (IH' := ortho_diamond_helper2 _ IH); clear IH; rename IH' into IH;
  apply ortho_validity in t_red_t' as H; destruct H as (H & _); apply validity_ty in H; destruct H as (ΓWf & _).

  (* var *)
  - ttinv t_red_t'. destruct t_red_t' as (B' & t'_eq_n & _ & lookup_n_B & _). 
    rewrite t'_eq_n in *. clear t'_eq_n t'.
    ttinv t_red_t''. destruct t_red_t'' as (_ & t''_eq_n & _ & _ & _).
    rewrite t''_eq_n in *. clear t''_eq_n t''.
    do 4 eexists. exists (var n). split; apply ortho_var; eauto. 


  (* sort *)
  - ttinv t_red_t'. destruct t_red_t' as (_ & t'_eq_sort & i_eq_ax & _). 
    rewrite t'_eq_sort in *. clear t'_eq_sort t'.
    ttinv t_red_t''. destruct t_red_t'' as (_ & t''_eq_sort & _ & _).
    rewrite t''_eq_sort in *. clear t''_eq_sort t''.
    do 4 eexists. exists (Sort l). split; apply ortho_sort; eauto.


  (* pi *)
  - rename t1 into A. rename t2 into B.
    ttinv t_red_t'. destruct t_red_t' as (A' & B' & t'_eq_pi & _ & A_red_A' & B_red_B' & _). 
    rewrite t'_eq_pi in *. clear t'_eq_pi t'.
    ttinv t_red_t''. destruct t_red_t'' as (A'' & B'' & t''_eq_pi & _ & A_red_A'' & B_red_B'' & _). 
    rewrite t''_eq_pi in *. clear t''_eq_pi t''.

    epose proof (IH_A := IH _ _ _ _ _ _ _ A_red_A' A_red_A''). destruct IH_A as (A''' & A'_red_A''' & A''_red_A'''). 
    shelve. Unshelve. simpl. lia.
    epose proof (IH_B := IH _ _ _ _ _ _ _ B_red_B' B_red_B''). destruct IH_B as (B''' & B'_red_B''' & B''_red_B'''). 
    shelve. Unshelve. simpl. lia.

    do 4 eexists. exists (Pi l l0 A''' B'''). 

    split; apply ortho_pi; auto.
    (* todo: how to optimise this?*)
    + eapply ortho_conv_in_ctx. apply conv_ccons. eapply refl_ctx. auto. eauto using ortho_to_conv. auto.
    + eapply ortho_conv_in_ctx. apply conv_ccons. eapply refl_ctx. auto. eauto using ortho_to_conv. auto.
    

  (* lam *)
  - rename t1 into A. rename t2 into B. rename t3 into u.
    ttinv t_red_t'. destruct t_red_t' as (A' & B' & u' & _ & _ & t'_eq_lam & A_conv_A' & B_conv_B' & u_red_u'). 
    rewrite t'_eq_lam in *. clear t'_eq_lam t'.
    ttinv t_red_t''. destruct t_red_t'' as (A'' & B'' & u'' & _ & _ & t''_eq_lam & A_conv_A'' & B_conv_B'' & u_red_u'').
    rewrite t''_eq_lam in *. clear t''_eq_lam t''.

    epose proof (IH_u := IH _ _ _ _ _ _ _ u_red_u' u_red_u''). destruct IH_u as (u''' & u'_red_u''' & u''_red_u'''). 
    shelve. Unshelve. simpl. lia.

    do 4 eexists. exists (lam l l0 A B u'''). split; apply ortho_lam; eauto using conv_sym. 
    + eapply (conv_in_ctx_conv (Γ,, (l, _))). apply conv_ccons. eapply refl_ctx. auto. eauto using ortho_to_conv. auto using conv_sym.
    + eapply (ortho_conv_in_ctx (Γ,, (l, _))). apply conv_ccons. eapply refl_ctx. auto. eauto using ortho_to_conv. auto using conv_sym.
      eapply ortho_conv. eauto. eauto.
    + eapply (conv_in_ctx_conv (Γ,, (l, _))). apply conv_ccons. eapply refl_ctx. auto. eauto using ortho_to_conv. auto using conv_sym.
    + eapply (ortho_conv_in_ctx (Γ,, (l, _))). apply conv_ccons. eapply refl_ctx. auto. eauto using ortho_to_conv. auto using conv_sym.
      eapply ortho_conv. eauto. eauto.


  (* app *)
  - rename t1 into A. rename t2 into B. rename t3 into u. rename t4 into v.
    ttinv t_red_t'. destruct t_red_t' as (i_eq & _ & [ t_red_t' | t_red_t' ]);
    ttinv t_red_t''; destruct t_red_t'' as (_ & _ & [ t_red_t'' | t_red_t'' ]).
    (* app-cong x app-cong *)
    + destruct t_red_t' as (A' & B' & u' & v' & t'_eq & A_conv_A' & B_conv_B' & u_red_u' & v_red_v').
      rewrite t'_eq in *. clear t'_eq t'.
      destruct t_red_t'' as (A'' & B'' & u'' & v'' & t''_eq & A_conv_A'' & B_conv_B'' & u_red_u'' & v_red_v'').
      rewrite t''_eq in *. clear t''_eq t''.

      epose proof (IH_u := IH _ _ _ _ _ _ _ u_red_u' u_red_u''). destruct IH_u as (u''' & u'_red_u''' & u''_red_u'''). 
      shelve. Unshelve. simpl. lia.
      epose proof (IH_v := IH _ _ _ _ _ _ _ v_red_v' v_red_v''). destruct IH_v as (v''' & v'_red_v''' & v''_red_v'''). 
      shelve. Unshelve. simpl. lia.

      do 4 eexists. exists (app l l0 A B u''' v'''). split; apply ortho_app; eauto using conv_sym.
      ++ eapply conv_in_ctx_conv. apply conv_ccons. eapply refl_ctx. auto. eauto using ortho_to_conv. auto using conv_sym.
      ++ eapply ortho_conv. eauto. apply conv_pi; eauto.
      ++ eapply ortho_conv. eauto. auto.
      ++ eapply conv_in_ctx_conv. apply conv_ccons. eapply refl_ctx. auto. eauto using ortho_to_conv. auto using conv_sym.
      ++ eapply ortho_conv. eauto. apply conv_pi; eauto.
      ++ eapply ortho_conv. eauto. auto.

    (* app-cong x beta *)
    + destruct t_red_t' as (A' & B' & u' & v' & t'_eq & A_conv_A' & B_conv_B' & u_red_u' & v_red_v').
      rewrite t'_eq in *. clear t'_eq t'.
      destruct t_red_t'' as (A0 & B0 & w & w'' & v'' & u_eq & A_conv_A0 & B_conv_B0 & w_red_w'' & v_red_v'' & t''_eq).
      rewrite t''_eq. clear t''_eq t''.
      
      rewrite u_eq in *. clear u_eq u. rewrite <- i_eq in *. clear l0 i_eq. 

      ttinv u_red_u'. destruct u_red_u' as (A0' & B0' & w' & _ & _ & u'_eq & A0_conv_A0' & B0_conv_B0' & w_red_w').

      rewrite u'_eq in *. clear u'_eq u'.
      
      rename w_red_w' into _w_red_w'.
      assert (Γ,, (l, A) ⊢< ty i > w ⟹ w' : B) as w_red_w'. 
      { eapply ortho_conv. eapply ortho_conv_in_ctx. apply conv_ccons. eapply refl_ctx. auto. 
        apply conv_sym. apply A_conv_A0. apply _w_red_w'. auto using conv_sym. }
      clear _w_red_w'.

      rename B0_conv_B0' into _B0_conv_B0'.
      assert (Γ,, (l, A) ⊢< Ax (ty i) > B0 ≡ B0' : Sort (ty i)) as B0_conv_B0'. 
      { eapply conv_in_ctx_conv. apply conv_ccons. eapply refl_ctx. auto. apply conv_sym. apply A_conv_A0. auto. }
      clear _B0_conv_B0'.

      epose proof (IH_w := IH _ _ _ _ _ _ _ w_red_w' w_red_w''). destruct IH_w as (w''' & w'_red_w''' & w''_red_w'''). 
      shelve. Unshelve. simpl. lia.
      epose proof (IH_v := IH _ _ _ _ _ _ _ v_red_v' v_red_v''). destruct IH_v as (v''' & v'_red_v''' & v''_red_v'''). 
      shelve. Unshelve. simpl. lia.

      do 4 eexists. exists (w''' <[ v''' ..]). split.
      ++ eapply ortho_beta. 
        +++ eauto using conv_sym, conv_trans. 
        +++ eapply conv_in_ctx_conv. apply conv_ccons. eapply refl_ctx. auto. apply A_conv_A'. eauto using conv_sym, conv_trans.
        +++ eapply ortho_conv_in_ctx. apply conv_ccons. eapply refl_ctx. auto. apply A_conv_A'. eapply ortho_conv. eauto. eauto using conv_sym, conv_trans.
        +++ eapply ortho_conv. eauto. eauto.
      ++ eapply ortho_subst_property. eapply (well_scons _ _ _ Γ l A). ssimpl. apply ortho_subst_id. auto. ssimpl. auto. eauto.
    
    (* beta x app-cong *)
    + admit. 

    (* beta x beta *)
    + destruct t_red_t' as (A0 & B0 & w & w' & v' & u_eq & _ & _ & w_red_w' & v_red_v' & t'_eq).
      rewrite t'_eq. clear t'_eq t'.
      destruct t_red_t'' as (A0_ & B0_ & w_ & w'' & v'' & u_eq_ & _ & _ & w_red_w'' & v_red_v'' & t''_eq).
      rewrite t''_eq. clear t''_eq t''.

      rewrite u_eq in *. clear u_eq u.
      inversion u_eq_.  rewrite <- H2 in *. clear H0 H1 H2 u_eq_ w_ A0_ B0_.

      epose proof (IH_w := IH _ _ _ _ _ _ _ w_red_w' w_red_w''). destruct IH_w as (w''' & w'_red_w''' & w''_red_w'''). 
      shelve. Unshelve. simpl. lia.
      epose proof (IH_v := IH _ _ _ _ _ _ _ v_red_v' v_red_v''). destruct IH_v as (v''' & v'_red_v''' & v''_red_v'''). 
      shelve. Unshelve. simpl. lia.

      do 4 eexists. exists (w''' <[ v''' .. ]).  split; eapply ortho_subst_property.
      ++ eapply (well_scons _ _ _ Γ l A). ssimpl. apply ortho_subst_id. auto. ssimpl. auto.
      ++ eauto.
      ++ eapply (well_scons _ _ _ Γ l A). ssimpl. apply ortho_subst_id. auto. ssimpl. auto.
      ++ eauto.
      

  (* Nat *)
  - ttinv t_red_t'. rewrite t_red_t'. clear t' t_red_t'. 
    ttinv t_red_t''. rewrite t_red_t''. clear t'' t_red_t''.
    do 4 eexists. exists Nat. split; apply ortho_nat; eauto.
  
  (* zero *)
  - ttinv t_red_t'. rewrite t_red_t'. clear t' t_red_t'. 
    ttinv t_red_t''. rewrite t_red_t''. clear t'' t_red_t''.
    do 4 eexists. exists zero. split; apply ortho_zero; eauto.

  (* succ *)
  - rename t into n. 
    ttinv t_red_t'. destruct t_red_t' as (n' & t'_eq & n_red_n'). 
    rewrite t'_eq. clear t'_eq t'.
    ttinv t_red_t''. destruct t_red_t'' as (n'' & t''_eq & n_red_n'').
    rewrite t''_eq. clear t''_eq t''.

    epose proof (IH_n := IH _ _ _ _ _ _ _ n_red_n' n_red_n''). destruct IH_n as (n''' & n'_red_n''' & n''_red_n'''). 
    shelve. Unshelve. simpl. lia.

    do 4 eexists. exists (succ n'''). split; eapply ortho_succ; eauto.

  (* rec *)
  - admit.   

Admitted.

Require Import Coq.Relations.Relation_Operators.
Require Import Coq.Relations.Relation_Definitions.

Definition ortho_redd Γ l A := clos_refl_trans _ (fun t u => ortho_red Γ l t u A).

Definition ortho_equiv Γ l A := clos_refl_sym_trans _ (fun t u => ortho_red Γ l t u A).

