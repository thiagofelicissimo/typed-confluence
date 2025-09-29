(** * Typing *)

From Stdlib Require Import Utf8 List Arith Bool Lia Wellfounded.Inverse_Image Wellfounded.Inclusion.
From TypedConfluence.autosubst
Require Import core unscoped AST SubstNotations RAsimpl AST_rasimpl.
From TypedConfluence Require Import Util BasicAST Weakenings Contexts Typing BasicMetaTheory. (*  Env Inst. *)
From Stdlib Require Import Setoid Morphisms Relation_Definitions.
Require Import Stdlib.Program.Equality.


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
      Γ ⊢< l > p_zero ⟹ p_zero' : P <[ zero .. ] -> 
      Γ ,, (ty 0 , Nat) ,, (l , P) ⊢< l > p_succ ⟹ p_succ' : P <[ (succ (var 1)) .: (shift >> (shift >> var)) ]  ->
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
  

where "Γ ⊢< l > t ⟹ u : A" := (ortho_red Γ l t u A).


Reserved Notation "Γ ⊢s σ ⟹ τ : Δ" (at level 50, σ, τ, Δ at next level).

Inductive ortho_subst (Γ : ctx) : ctx -> (nat -> term) -> (nat -> term) -> Prop :=
  | ortho_sempty (σ σ' : nat -> term) : 
    Γ ⊢s σ ⟹ σ' : ∙
  | ortho_scons (σ σ' : nat -> term) (Δ : ctx) l (A : term) :
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

Theorem ortho_subst_refl :
  forall Γ σ Δ,
  Γ ⊢s σ : Δ ->
  Γ ⊢s σ ⟹ σ : Δ.
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
  - eapply IHortho_red. eauto. eauto.
  - right. left. eauto.
  - right. right. do 5 eexists. split. reflexivity. split. reflexivity. eauto.
Qed.

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
    | rec _ _ _ _ _ => eapply ortho_rec_inv in h
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



Ltac ctx_conv_auto := 
  match goal with 
  | |- ⊢ ?Γ,, (?l, ?A) ≡ ?Γ,, (?l, ?B) =>
    apply conv_ccons; [ (eapply refl_ctx; eauto using ctx_cons, ctx_nil, type_nat, type_sort) | eauto using ortho_to_conv, conv_sym, conv_trans ]
  end.

Lemma red_scons_id Γ l A t t' : 
  Γ ⊢< l > t ⟹ t' : A ->
  Γ ⊢s t .. ⟹ t' .. : Γ ,, (l , A).
Proof.
  intro t_red_t'.
  apply ortho_scons. 
  - ssimpl. apply ortho_subst_refl. apply subst_id. 
    apply ortho_validity in t_red_t'. destruct t_red_t'. apply validity_ty in H.
    destruct H. auto.
  - ssimpl. auto.
Qed.

Lemma red_scons_id_2 Γ l A t t' u u' l' B : 
  Γ ⊢< l > t ⟹ t' : A ->
  Γ ⊢< l' > u ⟹ u' : B <[ t .. ] ->
  Γ ⊢s (u .: t ..) ⟹ (u' .: t' ..) : (Γ ,, (l , A)) ,, (l', B).
Admitted.

(* Lemma aux_ortho_0 Γ l A t u : 
  Γ ⊢< l > t ⟹ u : A ->
  Γ ⊢< Ax l > A : Sort l.
Admitted. *)

(* Lemma aux_ortho_3 Γ l A B : 
  Γ ⊢< Ax l > A ≡ B : Sort l ->
  ⊢ Γ ,, (l, B).
Admitted. *)

Lemma aux_ortho_1 Γ l A A' l' t u B B' : 
  Γ ,, (l , A) ⊢< l' > t ⟹ u : B ->
  Γ ⊢< Ax l > A ≡ A' : Sort l -> 
  Γ ,, (l , A) ⊢< Ax l' > B ≡ B' : Sort l' ->
  Γ ,, (l , A') ⊢< l' > t ⟹ u : B'.
Admitted.

Lemma aux_ortho_2 Γ l A A' l' t u B B' : 
  Γ ,, (l , A) ⊢< l' > t ≡ u : B ->
  Γ ⊢< Ax l > A ≡ A' : Sort l -> 
  Γ ,, (l , A) ⊢< Ax l' > B ≡ B' : Sort l' ->
  Γ ,, (l , A') ⊢< l' > t ≡ u : B'.
Admitted.

Lemma aux_ortho_3 Γ l A A' l' t u B : 
  Γ ,, (l , A) ⊢< l' > t ≡ u : B ->
  Γ ⊢< Ax l > A ≡ A' : Sort l -> 
  Γ ,, (l , A') ⊢< l' > t ≡ u : B.
Admitted.


Lemma aux_ortho_4 Γ l A A' l' t u B : 
  Γ ,, (l , A) ⊢< l' > t ⟹ u : B ->
  Γ ⊢< Ax l > A ≡ A' : Sort l -> 
  Γ ,, (l , A') ⊢< l' > t ⟹ u : B.
Admitted.


Lemma aux_ortho_6' Γ l P : 
  Γ ,, (ty 0, Nat) ⊢< Ax l > P : Sort l ->
  (Γ,, (ty 0, Nat)),, (l, P) ⊢s (succ (var 1) .: ↑ >> (↑ >> var)) : Γ ,, (ty 0, Nat).
Admitted.

Lemma aux_ortho_8 Γ k :
  Γ ⊢< ty 0 > k : Nat ->
  Γ ⊢s k .. : (Γ ,, (ty 0, Nat)).
Admitted.

Lemma ortho_validity_left Γ l t u A :
  Γ ⊢< l > t ⟹ u : A ->
  Γ ⊢< l > t : A.
Admitted.


Lemma ortho_validity_right Γ l t u A :
  Γ ⊢< l > t ⟹ u : A ->
  Γ ⊢< l > u : A.
Admitted.

Lemma aux_subst_auto Γ l P :
  ⊢ Γ -> 
  Γ ,, (ty 0, Nat) ⊢< Ax l > P : Sort l ->
  (Γ,, (ty 0, Nat)),, (l, P) ⊢s (succ (var 1) .: ↑ >> (↑ >> var)) : Γ,, (ty 0, Nat).
Proof.
  intros ΓWf PWt.
Admitted.

(* 
Ltac subst_auto := 
  ssimpl;
  match goal with 
  | |- ?Γ ⊢s var : ?Γ => 
    eauto using subst_id
  | |- ?Γ ⊢s (zero .: var) : ?Γ,, (ty 0, Nat) =>
    apply well_scons; [eauto using subst_id | eauto using type_zero]
  | H : _ ⊢< _ > ?k ⟹ _ : Nat |- ?Γ ⊢s (?k .: var) : ?Γ,, (ty 0, Nat) =>
    apply ortho_validity in H; destruct H; apply well_scons; [eauto using subst_id | eauto]
  | H : _ ⊢< _ > ?P ⟹ _ : _ |- (?Γ ,, (ty 0, Nat)) ,, (?l, ?P) ⊢s (succ (var 1) .: ↑ >> (↑ >> var)) : ?Γ ,, (ty 0, Nat) =>
    apply ortho_validity in H; destruct H; eauto using aux_subst_auto
  | _ => idtac
end.

Ltac conv_auto := 
  ssimpl;
  match goal with
  | H : ?Δ ⊢< Ax ?l > ?P ⟹ ?P' : Sort ?l |- ?Γ ⊢< Ax ?l > ?P <[ ?σ ] ≡ ?P' <[ ?σ ] : Sort ?l => 
    eapply (subst_ty Δ); [ try subst_auto | eauto using ortho_to_conv  ]
  | H : ?Δ ⊢< Ax ?l > ?P' ⟹ ?P : Sort ?l |- ?Γ ⊢< Ax ?l > ?P <[ ?σ ] ≡ ?P' <[ ?σ ] : Sort ?l => 
    eapply (subst_ty Δ); [ try subst_auto | eauto using ortho_to_conv, conv_sym ]
  | _ => eauto using ortho_to_conv, conv_sym, conv_trans
end.

Ltac use_auto :=
  match goal with
  (* | H : ?Γ ⊢< ?l > ?t ⟹ ?u : ?A |- ?Γ ⊢< ?l > ?t ⟹ ?u : ?A => exact H *)
  | H : ?Γ ⊢< ?l > ?t ⟹ ?u : ?A |- ?Δ ⊢< ?l > ?t ⟹ ?u : ?A =>
    apply (ortho_conv_in_ctx Γ Δ l t u A); [ ctx_conv_auto | exact H]
  | H : ?Γ ⊢< ?l > ?t ⟹ ?u : ?A |- ?Γ ⊢< ?l > ?t ⟹ ?u : ?B =>
    apply (ortho_conv Γ l A B t u); [exact H | conv_auto]
  | H : ?Γ ⊢< ?l > ?t ⟹ ?u : ?A |- ?Δ ⊢< ?l > ?t ⟹ ?u : ?B =>
    apply (ortho_conv_in_ctx Γ Δ l t u B); [ ctx_conv_auto | apply (ortho_conv Γ l A B t u); [exact H | conv_auto]]
  
  | H : ?Γ ⊢< ?l > ?t : ?A |- ?Δ ⊢< ?l > ?t : ?B =>
    apply (conv_in_ctx_ty Γ Δ l t B); [ ctx_conv_auto | apply (type_conv Γ l A B t); [exact H |  conv_auto]]

  | H : ?Γ ⊢< ?l > _ ⟹ ?t : ?A |- ?Γ ⊢< ?l > ?t : ?A =>
    apply ortho_validity in H; destruct H as (H1 & H2); eauto

  | H : ?Γ ⊢< ?l > _ ⟹ ?t : ?A |- ?Δ ⊢< ?l > ?t : ?B =>
    apply ortho_validity in H; destruct H as (H1 & H2);  
    apply (conv_in_ctx_ty Γ Δ l t B); [ ctx_conv_auto | apply (type_conv Γ l A B t); [exact H2 |  conv_auto]]

  | H : ?Γ ⊢< ?l > ?t ≡ ?u : ?A |- ?Δ ⊢< ?l > ?t ≡ ?u : ?A => 
    apply (conv_in_ctx_conv Γ Δ l t u A); [ ctx_conv_auto | exact H]
  | H : ?Γ ⊢< ?l > ?t ≡ ?u : ?A |- ?Δ ⊢< ?l > ?u ≡ ?t : ?A => 
    apply conv_sym; apply (conv_in_ctx_conv Γ Δ l t u A); [ ctx_conv_auto | exact H]
  | H : ?Δ ⊢< ?l > ?t ≡ ?u : ?P <[ ?n .. ] |- ?Δ ⊢< ?l > ?t ≡ ?u : ?P' <[ ?n .. ] => 
    eapply (ortho_conv Δ l _ _ t u) ; [exact H | (eapply subst_ty; eauto using ortho_to_conv)]
  | |- _ => idtac
  end. *)

(* TODO: think of some nice tactics to make the easy cases of the proof more direct *)


Theorem ortho_diamond_ty : 
  forall Γ i t t' t'' T,
    Γ ⊢< ty i > t ⟹ t' : T ->
    Γ ⊢< ty i > t ⟹ t'' : T ->
    exists t''', (Γ ⊢< ty i > t' ⟹ t''' : T) /\ (Γ ⊢< ty i > t'' ⟹ t''' : T).
Proof.
  intros Γ i t. generalize t Γ i. clear Γ i t. 
  
  refine (@well_founded_ind _ (fun t u => size t < size u) _ _ _). 
  eauto using wf_inverse_image, lt_wf.
  intros t IH Γ i t' t'' T t_red_t' t_red_t''.

  destruct t.
  all : eapply (ortho_diamond_helper _ _ _ _ _ _ t_red_t' t_red_t'').
  all : pose proof (IH' := ortho_diamond_helper2 _ IH); clear IH; rename IH' into IH.
  all : assert (⊢ Γ) as ΓWf by (apply ortho_validity_left in t_red_t'; apply validity_ty in t_red_t'; destruct t_red_t'; auto).

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

    destruct (IH A ltac:(simpl; lia) _ _ _ _ _ A_red_A' A_red_A'') as (A''' & A'_red_A''' & A''_red_A'''). 
    destruct (IH B ltac:(simpl; lia) _ _ _ _ _ B_red_B' B_red_B'') as (B''' & B'_red_B''' & B''_red_B''').
    do 4 eexists. exists (Pi l l0 A''' B'''). 
    split; apply ortho_pi; eauto using aux_ortho_4, ortho_to_conv, refl_ty. 

  (* lam *)
  - rename t1 into A. rename t2 into B. rename t3 into u.
    ttinv t_red_t'. destruct t_red_t' as (A' & B' & u' & _ & _ & t'_eq_lam & A_conv_A' & B_conv_B' & u_red_u'). 
    rewrite t'_eq_lam in *. clear t'_eq_lam t'.
    ttinv t_red_t''. destruct t_red_t'' as (A'' & B'' & u'' & _ & _ & t''_eq_lam & A_conv_A'' & B_conv_B'' & u_red_u'').
    rewrite t''_eq_lam in *. clear t''_eq_lam t''.

    destruct (IH u ltac:(simpl; lia) _ _ _ _ _ u_red_u' u_red_u'') as (u''' & u'_red_u''' & u''_red_u'''). 

    do 4 eexists. exists (lam l l0 A B u'''). 
    split; apply ortho_lam; eauto using aux_ortho_1, aux_ortho_3, conv_sym.

  (* app *)
  - rename t1 into A. rename t2 into B. rename t3 into u. rename t4 into v.
    ttinv t_red_t'. 
    destruct t_red_t' as 
      (i_eq & _ & [ (A' & B' & u' & v' & t'_eq & A_conv_A' & B_conv_B' & u_red_u' & v_red_v') 
      | (A0 & B0 & w & w' & v' & u_eq & _ & _ & w_red_w' & v_red_v' & t'_eq) ]);
    ttinv t_red_t''; 
    destruct t_red_t'' as 
      (_ & _ & [ (A'' & B'' & u'' & v'' & t''_eq & A_conv_A'' & B_conv_B'' & u_red_u'' & v_red_v'') 
      | (A0_ & B0_ & w_ & w'' & v'' & u_eq_ & A_conv_A0_ & B_conv_B0_ & w_red_w'' & v_red_v'' & t''_eq) ]);
    try rewrite t'_eq in *; clear t'_eq t'; rewrite t''_eq in *; clear t''_eq t'';
    try destruct (IH u ltac:(simpl; lia) _ _ _ _ _ u_red_u' u_red_u'') as (u''' & u'_red_u''' & u''_red_u'''); 
    try destruct (IH v ltac:(simpl; lia) _ _ _ _ _ v_red_v' v_red_v'') as (v''' & v'_red_v''' & v''_red_v''').
     
    (* app-cong x app-cong *)
    + do 4 eexists. exists (app l l0 A B u''' v'''). 
    split; apply ortho_app; eauto using conv_sym, aux_ortho_3, aux_ortho_1, conv_sym, ortho_conv, conv_pi.

    (* app-cong x beta *)
    + rename u_eq_ into u_eq. rename w_ into w. rename A0_ into A0. 
      rename B0_ into B0. rename A_conv_A0_ into A_conv_A0. rename B_conv_B0_ into B_conv_B0.

      rewrite u_eq in *. clear u_eq u. rewrite <- i_eq in *. clear l0 i_eq. 

      ttinv u_red_u'. destruct u_red_u' as (A0' & B0' & w' & _ & _ & u'_eq & A0_conv_A0' & B0_conv_B0' & w_red_w').

      rewrite u'_eq in *. clear u'_eq u'.
      
      rename w_red_w' into temp. 
      assert (Γ,, (l, A) ⊢< ty i > w ⟹ w' : B) as w_red_w'. {eauto using aux_ortho_1, aux_ortho_3, conv_sym. }
      clear temp.

      destruct (IH w ltac:(simpl; lia) _ _ _ _ _ w_red_w' w_red_w'') as (w''' & w'_red_w''' & w''_red_w'''). 

      do 4 eexists. exists (w''' <[ v''' ..]). split.
      ++ eapply ortho_beta; eauto 7 using conv_sym, conv_trans, ortho_conv, aux_ortho_4, aux_ortho_3.
      ++ eauto using red_scons_id, ortho_subst_property. 

    (* beta x app-cong *)
    + admit. 

    (* beta x beta *)
    + rewrite u_eq in *. clear u_eq u.
      inversion u_eq_.  rewrite <- H2 in *. clear A_conv_A0_ B_conv_B0_ H0 H1 H2 u_eq_ w_ A0_ B0_.

      destruct (IH w ltac:(simpl; lia) _ _ _ _ _ w_red_w' w_red_w'') as (w''' & w'_red_w''' & w''_red_w'''). 

      do 4 eexists. exists (w''' <[ v''' .. ]).  split; eauto using ortho_subst_property, red_scons_id.
      

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
      | (P'' & p_zero'' & p_succ'' & k & k'' & t''_eq & n_eq_ & P_red_P'' & p_zero_red_p_zero'' & p_succ_red_p_succ'' & k_red_k'')]]; 
    try rewrite t'_eq in *; try clear t'_eq t'; try rewrite t''_eq in *; try clear t''_eq t'';
    try rewrite n_eq in *; try rewrite n_eq_ in *; try clear n_eq n; try clear n_eq_ n;
    try destruct (IH P ltac:(simpl; lia) _ _ _ _ _ P_red_P' P_red_P'') as (P''' & P'_red_P''' & P''_red_P''');
    try destruct (IH p_zero ltac:(simpl; lia) _ _ _ _ _ p_zero_red_p_zero' p_zero_red_p_zero'') 
      as (p_zero''' & p_zero'_red_p_zero''' & p_zero''_red_p_zero''');
    try destruct (IH p_succ ltac:(simpl; lia) _ _ _ _ _ p_succ_red_p_succ' p_succ_red_p_succ'') 
      as (p_succ''' & p_succ'_red_p_succ''' & p_succ''_red_p_succ''').

    (* rec x rec *)
    + destruct (IH n ltac:(simpl; lia) _ _ _ _ _ n_red_n' n_red_n'') as (n''' & n'_red_n''' & n''_red_n'''). 
    
      do 4 eexists. exists (rec l P''' p_zero''' p_succ''' n'''). 
      split; eapply ortho_rec; 
      eauto 7 using ortho_conv, subst_ty, aux_ortho_8, type_zero, aux_ortho_1, ortho_to_conv, aux_ortho_6', ortho_validity_left.

    (* rec x rec_zero *)  
    + ttinv n_red_n'. rewrite n_red_n' in *. clear n' n_red_n'. 
    
    do 4 eexists. exists p_zero'''. split.
    2 : eauto.
    eapply ortho_rec_zero; 
    eauto 8 using aux_ortho_1, ortho_to_conv, subst_ty, ortho_conv, ortho_validity_left, 
              ortho_validity_right, aux_ortho_6', aux_ortho_8, type_zero.

    (* rec x rec_succ *)
    + ttinv n_red_n'. destruct n_red_n' as (k' & n'_eq & k_red_k'). rewrite n'_eq in *. clear n' n'_eq.
      epose proof (IH_k := IH k ltac:(simpl; lia) _ _ _ _ _ k_red_k' k_red_k''). destruct IH_k as (k''' & k'_red_k''' & k''_red_k'''). 
    
    do 4 eexists. exists ( p_succ''' <[ (rec l P''' p_zero''' p_succ''' k''') .: k''' ..]). split.
    ++ eapply ortho_rec_succ; 
        eauto 7 using aux_ortho_1, subst_ty, ortho_to_conv, aux_ortho_6', 
                  aux_ortho_8, ortho_conv, type_zero, ortho_validity_left.
    ++ eapply ortho_subst_property; eauto. apply red_scons_id_2; eauto. 
      eapply ortho_conv. 
      +++ eapply ortho_rec; 
        eauto 7 using aux_ortho_1, subst_ty, ortho_to_conv, aux_ortho_6', 
                  aux_ortho_8, ortho_conv, type_zero, ortho_validity_left.
      +++ eauto 6 using subst_ty, ortho_to_conv, conv_sym, aux_ortho_8, ortho_validity_left.
    
    (* rec_zero x rec *)
    + admit.

    (* rec_zero x rec_zero *)
    + do 4 eexists. exists p_zero'''. split; eauto.

    (* rec_zero x rec_succ *)
    + inversion n_eq_.

    (* rec_succ x rec *)
    + admit.

    (* rec_succ x rec_zero *)
    + inversion n_eq_.

    (* rec_succ x rec_succ *)
    + inversion n_eq_. rewrite H0 in *. clear m H0 n_eq_. 
      rename m' into k'. rename m_red_m' into k_red_k'.
      destruct (IH k ltac:(simpl; lia) _ _ _ _ _ k_red_k' k_red_k'') as (k''' & k'_red_k''' & k''_red_k''').
      do 4 eexists. exists (p_succ''' <[ rec l P''' p_zero''' p_succ''' k''' .: k''' .. ]). 
      split; eapply ortho_subst_property; eauto.
      all : apply red_scons_id_2; eauto.
      all : eapply ortho_conv. 
      1,3: eapply ortho_rec; 
        eauto 7 using ortho_rec, ortho_conv, subst_ty, aux_ortho_8, type_zero, 
                  ortho_to_conv, aux_ortho_1, ortho_validity_left, aux_ortho_6'.
      1,2: eauto 6 using subst_ty, ortho_to_conv, conv_sym, aux_ortho_8, ortho_validity_left.
Admitted.

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

(* Require Import Coq.Relations.Relation_Operators.
Require Import Coq.Relations.Relation_Definitions. *)

Inductive ortho_redd Γ l A : term -> term -> Prop := 
  | redd_step t u : Γ ⊢< l > t ⟹ u : A -> ortho_redd Γ l A t u
  | redd_trans t u v : ortho_redd Γ l A t v -> ortho_redd Γ l A v u -> ortho_redd Γ l A t u.


Notation "Γ ⊢< l > t ⟹* t' : A" := (ortho_redd Γ l A t t') (at level 50, l, t, t', A at next level).

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

Lemma equiv_to_conv Γ l t u A :
  Γ ⊢< l > t ≈ u : A ->
  Γ ⊢< l > t ≡ u : A.
Proof.
  intro t_equiv_u.
  induction t_equiv_u; eauto using ortho_to_conv, conv_trans, conv_sym.
Qed.


Lemma equiv_pi Γ i j A B A' B' :
      Γ ⊢< Ax i > A ≈ A' : Sort i →
      Γ ,, (i , A) ⊢< Ax j > B ≈ B' : Sort j →
      Γ ⊢< Ax (Ru i j) > Pi i j A B ≈ Pi i j A' B' : Sort (Ru i j).
Proof.
  intros A_equiv_A' B_equiv_B'.
  eapply equiv_trans.
  -  
  induction A_equiv_A'; induction B_equiv_B'.
 
Admitted.

Lemma equiv_lam Γ i j A B t A' B' t' :
      Γ ⊢< Ax i > A ≡ A' : Sort i →
      Γ ,, (i , A) ⊢< Ax j > B ≡ B': Sort j →
      Γ ,, (i , A) ⊢< j > t ≈ t' : B →
      Γ ⊢< Ru i j > lam i j A B t ≈ lam i j A' B' t' : Pi i j A B.
Proof.
  intros A_conv_A' B_conv_B' t_equiv_t'.
  induction t_equiv_t'.
  - apply equiv_step. econstructor; eauto.
  - eapply equiv_trans. eauto. eapply equiv_trans. 2:eauto. 
    apply equiv_sym. apply equiv_step. apply ortho_lam; eauto. 
    apply ortho_refl. apply equiv_to_conv in t_equiv_t'1.
    apply validity_conv in t_equiv_t'1. destruct t_equiv_t'1. auto.
  - eapply equiv_trans. eapply equiv_trans. 2:{ apply equiv_sym. apply IHt_equiv_t'. }
    + apply equiv_step. apply ortho_lam; eauto. 
      apply equiv_to_conv in t_equiv_t'. apply validity_conv in t_equiv_t'. destruct t_equiv_t'. eauto using ortho_refl.
    + apply equiv_step. apply ortho_lam; eauto. 
      apply equiv_to_conv in t_equiv_t'. apply validity_conv in t_equiv_t'. destruct t_equiv_t'. eauto using ortho_refl.
Qed.

Lemma equiv_app Γ i j A B t u A' B' t' u' :
      Γ ⊢< Ax i > A ≡ A' : Sort i →
      Γ ,, (i , A) ⊢< Ax j > B ≡ B': Sort j →
      Γ ⊢< Ru i j > t ≈ t' : Pi i j A B →
      Γ ⊢< i > u ≈ u' : A →
      Γ ⊢< j > app i j A B t u ≈ app i j A' B' t' u' : B <[ u .. ].
Admitted.

Lemma equiv_succ Γ t t' :
      Γ ⊢< ty 0 > t ≈ t' : Nat ->
      Γ ⊢< ty 0 > succ t ≈ succ t' : Nat.
Proof.
  intro t_equiv_t'. 
  induction t_equiv_t'.
  - apply equiv_step. apply ortho_succ. auto.
  - eapply equiv_trans; eauto.
  - apply equiv_sym; eauto.
Qed.

Lemma equiv_rec Γ l P p_zero p_succ t P' p_zero' p_succ' t' :
      Γ ,, (ty 0 , Nat) ⊢< Ax l > P ≈ P' : Sort l ->
      Γ ⊢< l > p_zero ≈ p_zero' : P <[ zero .. ] -> 
      Γ ,, (ty 0 , Nat) ,, (l , P) ⊢< l > p_succ ≈ p_succ' : P <[ (succ (var 1)) .: (shift >> (shift >> var)) ] ->
      Γ ⊢< ty 0 > t ≈ t' : Nat ->
      Γ ⊢< l > rec l P p_zero p_succ t ≈ rec l P' p_zero' p_succ' t' : P <[ t .. ].
Admitted.

Lemma equiv_cong Γ l A B t t' :
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

Lemma conv_to_equiv Γ l t u A :
  Γ ⊢< l > t ≡ u : A -> Γ ⊢< l > t ≈ u : A.
Proof.
  intro H. induction H.
  all : try solve [apply equiv_step; econstructor; eauto using refl_ty, ortho_refl ].
  - admit.
  - admit.
  - admit.
  - admit.
  - admit.
  - admit.
  - apply equiv_sym; eauto.
  - eapply equiv_trans; eauto.
Admitted.


Lemma confluence_aux Γ l t t' t'' A :
  Γ ⊢< l > t ⟹ t' : A -> 
  Γ ⊢< l > t ⟹* t'' : A ->
  exists t''', Γ ⊢< l > t' ⟹* t''' : A /\ Γ ⊢< l > t'' ⟹ t''' : A.
Proof.
  intros t_red_t' t_redd_t''. generalize t' t_red_t'. clear t' t_red_t'.
  induction t_redd_t''; intros.
  - pose (K := diamond _ _ _ _ _ _ H t_red_t'). destruct K as (t''' & K1 & K2). exists t'''. split; eauto using redd_step.
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

Corollary CR Γ l t u A :
  Γ ⊢< l > t ≡ u : A ->
  exists v, Γ ⊢< l > t ⟹* v : A /\ Γ ⊢< l > u ⟹* v : A.
Proof.
  intro H. apply conv_to_equiv in H. induction H.
  - exists u. split; apply redd_step; eauto. eapply ortho_refl. apply ortho_validity in H. destruct H. eauto.
  - destruct IHortho_equiv1 as (s & t_redd_s & v_redd_s).
    destruct IHortho_equiv2 as (w & v_redd_w & u_redd_w).
    pose (K := confluence _ _ _ _ _ _ v_redd_s v_redd_w).
    destruct K as (x & s_redd_x & w_redd_x).
    exists x. split; eauto using redd_trans.
  - destruct IHortho_equiv as (v & u_redd_v & t_redd_v). exists v. eauto.
Qed.

Lemma redd_conv_in_ctx Γ Δ l t u A :
  ⊢ Γ ≡ Δ -> Γ ⊢< l > t ⟹* u : A -> Δ ⊢< l > t ⟹* u : A.
Proof.
  intros Γ_equiv_Δ t_redd_u.
  induction t_redd_u.
  - apply redd_step. eapply ortho_conv_in_ctx; eauto.
  - eapply redd_trans; eauto.
Qed.

Lemma reduce_pi Γ l l1 l2 A B T U :
  Γ ⊢< l > Pi l1 l2 A B ⟹* T : U ->
  exists A' B',
  T = Pi l1 l2 A' B' /\
  Γ ⊢< Ax l1 > A ⟹* A' : Sort l1 /\
  Γ ,, (l1, A) ⊢< Ax l2 > B ⟹* B' : Sort l2.
Proof.
  intros pi_red_T.
  dependent induction pi_red_T.
  - ttinv H. destruct H as (A' & B' & T_eq & _ & A_red & B_red & _). do 2 eexists. split; eauto. split; apply redd_step; eauto.
  - destruct (IHpi_red_T1 l1 l2 A B eq_refl) as (A'' & B'' & v_eq & A_red & B_red). 
    rewrite v_eq in *. clear v_eq v.
    destruct (IHpi_red_T2 l1 l2 A'' B'' eq_refl) as (A''' & B''' & u_eq & A''_red & B''_red).
    rewrite u_eq in *. clear u_eq u.
    exists A'''. exists B'''. split. eauto. split; eapply redd_trans; eauto.
    apply redd_to_conv in A_red. eapply (redd_conv_in_ctx (Γ ,, (l1, A''))); eauto.
     ctx_conv_auto. 
    apply validity_conv in A_red. destruct A_red. apply validity_ty in H. destruct H. auto.
Qed.


Corollary pi_inj Γ l l0 l1 l2 l3 A B A' B' T : 
  Γ ⊢< l > Pi l0 l1 A B ≡ Pi l2 l3 A' B' : T -> 
  l0 = l2 /\ l1 = l3 /\ Γ ⊢< Ax l0 > A ≡ A' : Sort l0 /\ Γ ,, (l0, A) ⊢< Ax l1 > B ≡ B' : Sort l1.
Proof.
  intro Pi_eq.
  apply CR in Pi_eq.
  destruct Pi_eq as (v & Pi_red_1 & Pi_red_2).
  apply reduce_pi in Pi_red_1.
  destruct Pi_red_1 as (A0 & B0 & v_eq & A_redd_A0 & B_redd_B0).
  apply reduce_pi in Pi_red_2.
  destruct Pi_red_2 as (A1 & B1 & v_eq_ & A'_redd_A1 & B'_redd_B1).
  rewrite v_eq in *. inversion v_eq_. 
  rewrite H0 in *. rewrite H1 in *. rewrite H2 in *. rewrite H3 in *.
  clear A0 B0 H0 H1 H2 H3 v_eq v. 
  apply redd_to_conv in A_redd_A0, B_redd_B0, A'_redd_A1, B'_redd_B1.
  split; split; split; auto.
  - eauto using conv_trans, conv_sym.
  - eapply conv_trans. apply B_redd_B0. eauto using aux_ortho_3, conv_sym.
Qed.