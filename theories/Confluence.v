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
          p_succ' <[ t' .: (rec l P' p_zero' p_succ' t') ..] : P <[ (succ t) .. ]
  

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


Require Import Stdlib.Program.Equality.

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
      t = p_succ' <[ n' .: (rec l P' p_zero' p_succ' n') ..] ∧ u = succ n ∧
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
  (* | H : ?Γ ⊢< ?l > ?t ⟹ ?u : ?A |- ⊢ ?Γ ≡ ?Γ => eapply refl_ctx; eauto using H, ortho_validity, validity_ty
  | H : ?Γ ⊢< ?l > ?t : ?A |- ⊢ ?Γ ≡ ?Γ => eapply refl_ctx; eauto using H, validity_ty
  | H : ?Γ ⊢< ?l > ?t ≡ ?u : ?A |- ⊢ ?Γ ≡ ?Γ => eapply refl_ctx; eauto using H, ortho_validity, validity_conv, validity_ty
  | H : ⊢ ?Γ |- ⊢ ?Γ ≡ ?Γ => eapply refl_ctx; eauto using H
   
   *)
  | |- ⊢ ?Γ,, (?l, ?A) ≡ ?Γ,, (?l, ?B) =>
    apply conv_ccons; [ (eapply refl_ctx; eauto using ctx_cons, ctx_nil, type_nat) | eauto using ortho_to_conv, conv_sym, conv_trans ]
  end.


Ltac use_auto :=
  match goal with
  (* | H : ?Γ ⊢< ?l > ?t ⟹ ?u : ?A |- ?Γ ⊢< ?l > ?t ⟹ ?u : ?A => exact H *)
  | H : ?Γ ⊢< ?l > ?t ⟹ ?u : ?A |- ?Δ ⊢< ?l > ?t ⟹ ?u : ?A =>
    apply (ortho_conv_in_ctx Γ Δ l t u A); [ ctx_conv_auto | exact H]
  | H : ?Γ ⊢< ?l > ?t ⟹ ?u : ?A |- ?Γ ⊢< ?l > ?t ⟹ ?u : ?B =>
    apply (ortho_conv Γ l A B t u); [exact H | idtac]
  | H : ?Γ ⊢< ?l > ?t ⟹ ?u : ?A |- ?Δ ⊢< ?l > ?t ⟹ ?u : ?B =>
    apply (ortho_conv_in_ctx Γ Δ l t u B); [ ctx_conv_auto | apply (ortho_conv Γ l A B t u); [exact H | eauto using ortho_to_conv, conv_sym, conv_trans]]
  | H : ?Γ ⊢< ?l > ?t : ?A |- ?Δ ⊢< ?l > ?t : ?B =>
    apply (conv_in_ctx_ty Γ Δ l t B); [ ctx_conv_auto | apply (type_conv Γ l A B t); [exact H | eauto using ortho_to_conv, conv_sym, conv_trans]]
  (* | H : ?Γ ⊢< ?l > ?t ≡ ?u : ?A |- H : ?Γ ⊢< ?l > ?t ≡ ?u : ?A *)
  | H : ?Γ ⊢< ?l > ?t ≡ ?u : ?A |- ?Δ ⊢< ?l > ?t ≡ ?u : ?A => 
    apply (conv_in_ctx_conv Γ Δ l t u A); [ ctx_conv_auto | exact H]
  | H : ?Γ ⊢< ?l > ?t ≡ ?u : ?A |- ?Δ ⊢< ?l > ?u ≡ ?t : ?A => 
    apply conv_sym; apply (conv_in_ctx_conv Γ Δ l t u A); [ ctx_conv_auto | exact H]
  | |- _ => idtac
  end.

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

    epose proof (IH_A := IH A ltac:(simpl; lia) _ _ _ _ _ A_red_A' A_red_A''). destruct IH_A as (A''' & A'_red_A''' & A''_red_A'''). 
    epose proof (IH_B := IH B ltac:(simpl; lia) _ _ _ _ _ B_red_B' B_red_B''). destruct IH_B as (B''' & B'_red_B''' & B''_red_B''').
    do 4 eexists. exists (Pi l l0 A''' B'''). 
    split; apply ortho_pi; eauto; use_auto.

  (* lam *)
  - rename t1 into A. rename t2 into B. rename t3 into u.
    ttinv t_red_t'. destruct t_red_t' as (A' & B' & u' & _ & _ & t'_eq_lam & A_conv_A' & B_conv_B' & u_red_u'). 
    rewrite t'_eq_lam in *. clear t'_eq_lam t'.
    ttinv t_red_t''. destruct t_red_t'' as (A'' & B'' & u'' & _ & _ & t''_eq_lam & A_conv_A'' & B_conv_B'' & u_red_u'').
    rewrite t''_eq_lam in *. clear t''_eq_lam t''.

    epose proof (IH_u := IH u ltac:(simpl; lia) _ _ _ _ _ u_red_u' u_red_u''). destruct IH_u as (u''' & u'_red_u''' & u''_red_u'''). 

    do 4 eexists. exists (lam l l0 A B u'''). split; apply ortho_lam; eauto using conv_sym; use_auto.

  (* app *)
  - rename t1 into A. rename t2 into B. rename t3 into u. rename t4 into v.
    ttinv t_red_t'. destruct t_red_t' as (i_eq & _ & [ (A' & B' & u' & v' & t'_eq & A_conv_A' & B_conv_B' & u_red_u' & v_red_v') 
                                                     | (A0 & B0 & w & w' & v' & u_eq & _ & _ & w_red_w' & v_red_v' & t'_eq) ]);
    ttinv t_red_t''; destruct t_red_t'' as (_ & _ & [ (A'' & B'' & u'' & v'' & t''_eq & A_conv_A'' & B_conv_B'' & u_red_u'' & v_red_v'') 
                                                    | (A0_ & B0_ & w_ & w'' & v'' & u_eq_ & A_conv_A0_ & B_conv_B0_ & w_red_w'' & v_red_v'' & t''_eq) ]);
    try rewrite t'_eq in *; clear t'_eq t'; rewrite t''_eq in *; clear t''_eq t'';
    try epose proof (IH_u := IH u ltac:(simpl; lia) _ _ _ _ _ u_red_u' u_red_u''); try destruct IH_u as (u''' & u'_red_u''' & u''_red_u'''); 
    try epose proof (IH_v := IH v ltac:(simpl; lia) _ _ _ _ _ v_red_v' v_red_v''); try destruct IH_v as (v''' & v'_red_v''' & v''_red_v''').
     
    (* app-cong x app-cong *)
    + do 4 eexists. exists (app l l0 A B u''' v'''). split; apply ortho_app; eauto using conv_sym; use_auto; eauto; apply conv_pi; eauto.

    (* app-cong x beta *)
    + rename u_eq_ into u_eq. rename w_ into w. rename A0_ into A0. rename B0_ into B0. rename A_conv_A0_ into A_conv_A0. rename B_conv_B0_ into B_conv_B0.

      rewrite u_eq in *. clear u_eq u. rewrite <- i_eq in *. clear l0 i_eq. 

      ttinv u_red_u'. destruct u_red_u' as (A0' & B0' & w' & _ & _ & u'_eq & A0_conv_A0' & B0_conv_B0' & w_red_w').

      rewrite u'_eq in *. clear u'_eq u'.
      
      rename w_red_w' into temp. assert (Γ,, (l, A) ⊢< ty i > w ⟹ w' : B) as w_red_w'. {use_auto. use_auto. } clear temp.
      rename B0_conv_B0' into temp. assert (Γ,, (l, A) ⊢< Ax (ty i) > B0 ≡ B0' : Sort (ty i)) as B0_conv_B0'.  {use_auto. } clear temp.

      try epose proof (IH_w := IH w ltac:(simpl; lia) _ _ _ _ _ w_red_w' w_red_w''); try destruct IH_w as (w''' & w'_red_w''' & w''_red_w'''). 

      do 4 eexists. exists (w''' <[ v''' ..]). split.
      ++ eapply ortho_beta;  use_auto ; eauto using conv_sym, conv_trans. 
        eapply (conv_in_ctx_conv (Γ ,, (l, A))). ctx_conv_auto. eauto using conv_sym, conv_trans.
      ++ eapply ortho_subst_property. eapply (ortho_scons _ _ _ Γ l A). ssimpl. apply ortho_subst_id. auto. ssimpl. auto. eauto.
    
    (* beta x app-cong *)
    + admit. 

    (* beta x beta *)
    + rewrite u_eq in *. clear u_eq u.
      inversion u_eq_.  rewrite <- H2 in *. clear A_conv_A0_ B_conv_B0_ H0 H1 H2 u_eq_ w_ A0_ B0_.

      try epose proof (IH_w := IH w ltac:(simpl; lia) _ _ _ _ _ w_red_w' w_red_w''); try destruct IH_w as (w''' & w'_red_w''' & w''_red_w'''). 

      do 4 eexists. exists (w''' <[ v''' .. ]).  split; eapply ortho_subst_property; eauto. 
      ++ eapply (ortho_scons _ _ _ Γ l A). ssimpl. apply ortho_subst_id. auto. ssimpl. auto.
      ++ eapply (ortho_scons _ _ _ Γ l A). ssimpl. apply ortho_subst_id. auto. ssimpl. auto.
      

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

    epose proof (IH_n := IH n ltac:(simpl; lia) _ _ _ _ _ n_red_n' n_red_n''). destruct IH_n as (n''' & n'_red_n''' & n''_red_n'''). 

    do 4 eexists. exists (succ n'''). split; eapply ortho_succ; eauto.

  (* rec *)
  - rename t1 into P. rename t2 into p_zero. rename t3 into p_succ. rename t4 into n.
    ttinv t_red_t'. ttinv t_red_t''. 
    destruct t_red_t' as [(P' & p_zero' & p_succ' & n' & t'_eq & P_red_P' & p_zero_red_p_zero' & p_succ_red_p_succ' & n_red_n') 
                        | [ (p_zero' & t'_eq & n_eq & p_zero_red_p_zero')
                        | t_red_t']]; 
    destruct t_red_t'' as [(P'' & p_zero'' & p_succ'' & n'' & t''_eq & P_red_P'' & p_zero_red_p_zero'' & p_succ_red_p_succ'' & n_red_n'') 
                        | [ (p_zero'' & t''_eq & _n_eq & p_zero_red_p_zero'')
                        | t_red_t'']]; 
    try rewrite t'_eq in *; try clear t'_eq t'; try rewrite t''_eq in *; try clear t''_eq t'';
    try epose proof (IH_P := IH P ltac:(simpl; lia) _ _ _ _ _ P_red_P' P_red_P''); try  destruct IH_P as (P''' & P'_red_P''' & P''_red_P''');
    try epose proof (IH_p_zero := IH p_zero ltac:(simpl; lia) _ _ _ _ _ p_zero_red_p_zero' p_zero_red_p_zero'');
    try destruct IH_p_zero as (p_zero''' & p_zero'_red_p_zero''' & p_zero''_red_p_zero''');
    try epose proof (IH_p_succ := IH p_succ ltac:(simpl; lia) _ _ _ _ _ p_succ_red_p_succ' p_succ_red_p_succ'');
    try destruct IH_p_succ as (p_succ''' & p_succ'_red_p_succ''' & p_succ''_red_p_succ''').
    (* try epose proof (IH_n := IH n ltac:(simpl; lia) _ _ _ _ _ n_red_n' n_red_n''); try destruct IH_n as (n''' & n'_red_n''' & n''_red_n''').  *)


    + epose proof (IH_n := IH n ltac:(simpl; lia) _ _ _ _ _ n_red_n' n_red_n''). destruct IH_n as (n''' & n'_red_n''' & n''_red_n'''). 

      assert (Γ,, (ty 0, Nat) ⊢< Ax l > P : Sort l) as WtP. { apply ortho_validity in P_red_P' as H. destruct H. eauto. }
      assert (⊢ (Γ,, (ty 0, Nat)),, (l, P)). {apply ctx_cons; eauto. apply ctx_cons; eauto using type_nat.  }
    
      do 4 eexists. exists (rec l P''' p_zero''' p_succ''' n'''). split; eapply ortho_rec; eauto; use_auto; eapply subst_ty; eauto using ortho_to_conv.
      ++  eapply well_scons. ssimpl. admit. ssimpl. eauto using type_zero.
      ++  eapply well_scons. ssimpl. admit. ssimpl. eapply type_succ. eapply (type_var _ _ _ Nat); eauto.
      ++  eapply well_scons. ssimpl. admit. ssimpl. eauto using type_zero.
      ++  eapply well_scons. ssimpl. admit. ssimpl. eapply type_succ. eapply (type_var _ _ _ Nat); eauto.
    + rewrite _n_eq in *. clear n _n_eq. ttinv n_red_n'. rewrite n_red_n' in *. clear n' n_red_n'. 
    
    do 4 eexists. exists p_zero'''. split. 
      ++ eapply ortho_rec_zero; eauto. apply ortho_validity in P_red_P'. destruct P_red_P'. eauto. admit. 
        apply ortho_validity in p_succ_red_p_succ'. destruct p_succ_red_p_succ'. use_auto.
        eapply subst_ty. 2:{eauto using ortho_to_conv. } apply well_scons. ssimpl. admit. ssimpl. apply type_succ. eapply (type_var _ _ _ Nat). 
        admit. eauto.
      ++ eauto.
    + 



Admitted.

Require Import Coq.Relations.Relation_Operators.
Require Import Coq.Relations.Relation_Definitions.

Definition ortho_redd Γ l t u A := clos_refl_trans _ (fun t u => ortho_red Γ l t u A) t u.

Definition ortho_equiv Γ l t u A := clos_refl_sym_trans _ (fun t u => ortho_red Γ l t u A) t u.


Notation "Γ ⊢< l > t ⟹* t' : A" := (ortho_redd Γ l t t' A) (at level 50, l, t, t', A at next level).
Notation "Γ ⊢< l > t ≈ t' : A" := (ortho_equiv Γ l t t' A) (at level 50, l, t, t', A at next level).

Lemma conv_to_equiv Γ l t u A :
  Γ ⊢< l > t ≡ u : A -> Γ ⊢< l > t ≈ u : A.
Proof.
Admitted.

Corollary CR Γ l t u A :
  Γ ⊢< l > t ≈ u : A ->
  exists v, Γ ⊢< l > t ⟹* v : A /\ Γ ⊢< l > u ⟹* v : A.
Proof.
Admitted.

Lemma reduce_pi Γ l l1 l2 A B T U :
  Γ ⊢< l > Pi l1 l2 A B ⟹* T : U ->
  exists A' B',
  T = Pi l1 l2 A' B' /\
  Γ ⊢< Ax l1 > A ⟹* A' : Sort l1 /\
  Γ ,, (l1, A) ⊢< Ax l2 > B ⟹* B' : Sort l2.
Proof.
  intros pi_red_T.
  dependent induction pi_red_T; try rename y into T.
  - ttinv H. destruct H as (A' & B' & T_eq & _ & A_red & B_red & _). do 2 eexists. split; eauto. split; apply rt_step; eauto.
  - exists A. exists B. split. reflexivity. split; apply rt_refl.
  - destruct (IHpi_red_T1 l1 l2 A B eq_refl) as (A'' & B'' & T_eq & A_red & B_red). 
    rewrite T_eq in *. clear T_eq T.
    destruct (IHpi_red_T2 l1 l2 A'' B'' eq_refl) as (A''' & B''' & T_eq & A''_red & B''_red).
    exists A'''. exists B'''. split. eauto. split. eapply rt_trans; eauto.
    eapply rt_trans; eauto. use_auto.
    admit.
Admitted.


Corollary pi_inj Γ l l0 l1 A B A' B' : 
  Γ ⊢< l > Pi l0 l1 A B ≡ Pi l0 l1 A' B' : Sort (Ru l0 l1) -> 
  Γ ⊢< Ax l0 > A ≡ A' : Sort l0 /\ Γ ,, (l0, A) ⊢< Ax l1 > B ≡ B' : Sort l1.
Proof.
  intro Pi_eq.
  apply conv_to_equiv in Pi_eq.
  apply CR in Pi_eq.
  destruct Pi_eq as (v & Pi_red_1 & Pi_red_2).
  apply reduce_pi in Pi_red_1.
  destruct Pi_red_1 as (A0 & B0 & v_eq & A_redd_A0 & B_redd_B0).
  apply reduce_pi in Pi_red_2.
  destruct Pi_red_2 as (A1 & B1 & v_eq_ & A'_redd_A1 & B'_redd_B1).
  rewrite v_eq in *. inversion v_eq_. rewrite H0 in *. rewrite H1 in *.
  clear A0 B0 H0 H1 v_eq v.
  admit.
Admitted.
