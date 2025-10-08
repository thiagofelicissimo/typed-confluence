
From Stdlib Require Import Utf8 List Arith Bool Lia Wellfounded.Inverse_Image Wellfounded.Inclusion.
From TypedConfluence.autosubst
Require Import core unscoped AST SubstNotations RAsimpl AST_rasimpl.
From TypedConfluence Require Import Util BasicAST Weakenings Contexts Typing BasicMetaTheory Confluence ConversionChecking. (*  Env Inst. *)
From Stdlib Require Import Setoid Morphisms Relation_Definitions.
Require Import Stdlib.Program.Equality.
Import CombineNotations.


Inductive cterm : Type := 
| cann : cterm -> cterm -> cterm 
| cvar : nat -> cterm 
| cSort : level -> cterm 

| cPi : cterm -> cterm -> cterm 
| capp : cterm -> cterm -> cterm 
| clam : cterm -> cterm 

| cNat : cterm
| czero : cterm 
| csucc : cterm -> cterm
| crec : cterm -> cterm -> cterm -> cterm -> cterm.

Reserved Notation "Γ ⊢< l > M ⇒ T ↣ t" (at level 50, l, M, T, t at next level).
Reserved Notation "Γ ⊢< l > M ⇐ T ↣ t" (at level 50, l, M, T, t at next level).


Definition box_if_prop l t := 
    match l with 
    | prop => box 
    | ty _ => t 
    end.

Definition app_box t u := 
    match t with 
    | box => box 
    | _ => app prop prop box box t u
    end.

Definition lam_box t := 
    match t with 
    | box => box 
    | _ => lam prop prop box box t
    end.

Definition rec_box l P p_zero p_succ k := 
    match l with 
    | prop => box 
    | _ => rec l P p_zero p_succ k
    end.



Inductive infer : ctx -> level -> cterm → term -> term → Prop :=
| infer_var Γ x l A :
    nth_error Γ x = Some (l , A) →
    Γ ⊢< l > cvar x ⇒ ((plus (S x)) ⋅ A) ↣ box_if_prop l (var x)

| infer_Sort Γ l : 
    Γ ⊢< Ax (Ax l) > cSort l ⇒ Sort (Ax l) ↣ Sort l

| infer_pi Γ i j T U MA MB A B : 
    Γ ⊢< Ax i > MA ⇒ T ↣ A -> 
    T -->> Sort i ->
    Γ ,, (i , A) ⊢< Ax j > MB ⇒ U ↣ B -> 
    U -->> Sort j ->
    Γ ⊢< Ax (Ru i j) > cPi MA MB ⇒ Sort (Ru i j) ↣ Pi i j A B

| infer_app Γ l i j T Mt Mu t u A B :
    Γ ⊢< l > Mt ⇒ T ↣ t -> 
    T -->> Pi i j A B -> 
    Γ ⊢< i > Mu ⇐ A ↣ u -> 
    Γ ⊢< j > capp Mt Mu ⇒ B <[ u..] ↣ app_box t u

| infer_Nat Γ : 
    Γ ⊢< ty 1 > cNat ⇒ Sort (ty 0) ↣ Nat

| infer_zero Γ : 
    Γ ⊢< ty 0 > czero ⇒ Nat ↣ zero

| infer_succ Γ Mt t l T :
    Γ ⊢< l > Mt ⇒ T ↣ t -> 
    T -->> Nat ->
    Γ ⊢< ty 0 > csucc Mt ⇒ Nat ↣ succ t

| infer_rec Γ MP P Mp_zero p_zero Mp_succ p_succ Mk k l l' T :
    Γ ,, (ty 0, Nat) ⊢< l' > MP ⇒ T ↣ P -> 
    T -->> Sort l ->
    Γ ⊢< l > Mp_zero ⇐ P <[ zero ..] ↣ p_zero ->
    Γ ,, (ty 0 , Nat) ,, (l , P) ⊢< l > Mp_succ ⇐ P <[ (succ (var 1)) .: (shift >> (shift >> var)) ] ↣ p_succ -> 
    Γ ⊢< ty 0 > Mk ⇐ Nat ↣ k ->
    Γ ⊢< l > crec MP Mp_zero Mp_succ Mk ⇒ P <[ k ..] ↣ rec_box l P p_zero p_succ k

| infer_ann Γ MA Mt t l A T i :
    Γ ⊢< l > MA ⇒ T ↣ A ->
    T -->> Sort i ->
    Γ ⊢< i > Mt ⇐ A ↣ t -> 
    Γ ⊢< i > cann Mt MA ⇒ A ↣ t

with check : ctx -> level -> cterm -> term → term → Prop :=
| check_conv Γ Mt t l l' T T' U U' :
    Γ ⊢< l > Mt ⇒ T ↣ t -> 
    l = l' ->
    T -->> T' -> nf T' -> 
    U -->> U' -> nf U' -> 
    T' = U' ->
    Γ ⊢< l' > Mt ⇐ U ↣ t 
    
| check_lam Γ l Mt t T i j A B :
    T -->> Pi i j A B ->
    Γ ,, (i, A) ⊢< j > Mt ⇐ B ↣ t -> 
    Γ ⊢< l > clam Mt ⇐ T ↣ lam_box t

where "Γ ⊢< l > M ⇒ T ↣ t" := (infer Γ l M T t)
and   "Γ ⊢< l > M ⇐ T ↣ t" := (check Γ l M T t).


Scheme infer_mut := Induction for infer Sort Prop
with check_mut := Induction for check Sort Prop.
Combined Scheme infer_check_mutind from infer_mut, check_mut.


Definition erase_ctx (Γ : ctx) := 
    List.map (fun x => (fst x, erasure (Ax (fst x)) (snd x))) Γ.

    
Lemma var_in_erased_ctx Γ x l A : 
    nth_error (erase_ctx Γ) x = Some (l, A) -> 
    exists A', A = erasure (Ax l) A' /\ nth_error Γ x = Some (l, A').
Proof.
    intro H.
    unfold erase_ctx in H.
    rewrite nth_error_map in H.
    destruct (nth_error Γ x); inversion H.
    exists (snd p). split; eauto. destruct p; eauto.
Qed.

Lemma reduce_to_sort Γ l t A j :
    Γ ⊢< l > t : A -> 
    erasure (Ax l) A -->> Sort j -> 
    Γ ⊢< Ax j > t : Sort j /\ l = Ax j.
Proof.
    intros t_Wt erasure_red.
    eapply subject_reduction_redd in erasure_red as (_sort & TA_eq_sort & erasure_sort_eq_sort) ; eauto using validity_ty_ty.
    destruct _sort; dependent destruction erasure_sort_eq_sort.
    apply validity_conv_right in TA_eq_sort as Sort_wt. 
    apply type_inv_sort' in Sort_wt as (_ & l_eq_0 & _).
    apply Ax_inj in l_eq_0. dependent destruction l_eq_0.
    split; eauto using type_conv.
Qed.

Lemma reduce_to_pi Γ l t T i j A B :
    Γ ⊢< l > t : T -> 
    erasure (Ax l) T -->> Pi i j A B -> 
    exists A' B', A = erasure (Ax i) A' /\ B = erasure (Ax j) B' /\ Γ ⊢< Ru i j > t : Pi i j A' B' /\ l = Ru i j.
Proof.
    intros t_Wt erasure_red.
    eapply subject_reduction_redd in erasure_red as (_pi & TA_eq_pi & erasure_pi_eq_pi) ; eauto using validity_ty_ty.
    destruct _pi; dependent destruction erasure_pi_eq_pi.
    apply validity_conv_right in TA_eq_pi as pi_wt. 
    apply type_inv_pi' in pi_wt as (_ & _ & _ & l_eq_ru & _).
    apply Ax_inj in l_eq_ru. dependent destruction l_eq_ru.
    exists _pi1. exists _pi2.
    split; eauto using type_conv.
Qed.

Lemma reduce_to_pi' Γ l T i j A B :
    Γ ⊢< Ax l > T : Sort l -> 
    erasure (Ax l) T -->> Pi i j A B -> 
    exists A' B', A = erasure (Ax i) A' /\ B = erasure (Ax j) B' /\ Γ ⊢< Ax (Ru i j) > T ≡ Pi i j A' B' : Sort (Ru i j) /\ l = Ru i j.
Proof.
    intros t_Wt erasure_red.
    eapply subject_reduction_redd in erasure_red as (_pi & TA_eq_pi & erasure_pi_eq_pi) ; eauto using validity_ty_ty.
    destruct _pi; dependent destruction erasure_pi_eq_pi.
    apply validity_conv_right in TA_eq_pi as pi_wt. 
    apply type_inv_pi' in pi_wt as (_ & _ & _ & l_eq_ru & _).
    apply Ax_inj in l_eq_ru. dependent destruction l_eq_ru.
    exists _pi1. exists _pi2.
    split; eauto using type_conv.
Qed.


Lemma reduce_to_nat Γ l t A :
    Γ ⊢< l > t : A -> 
    erasure (Ax l) A -->> Nat -> 
    Γ ⊢< ty 0 > t : Nat /\ l = ty 0.
Proof.
    intros t_Wt erasure_red.
    eapply subject_reduction_redd in erasure_red as (_nat & TA_eq_nat & erasure_nat_eq_nat) ; eauto using validity_ty_ty.
    destruct _nat; dependent destruction erasure_nat_eq_nat.
    apply validity_conv_right in TA_eq_nat as Nat_wt. 
    apply type_inv_nat' in Nat_wt as (_ & l_eq_0 & _).
    destruct l; inversion l_eq_0.
    rewrite <- H0. eauto using type_conv.
Qed.

(* Lemma app_box_app Γ l A i t u :
    Γ ⊢< l > t : A ->
    app_box (erasure (ty i) t) u = app prop prop box box (erasure (ty i) t) u.
Proof.
    intro Wt.
    destruct t; auto.
    apply type_inv_box in Wt. inversion Wt.
Qed. *)

Lemma app_box_erasure Γ l T i j A B t u : 
    Γ ⊢< l > t : T ->
    erasure j (app i j A B t u) = app_box (erasure (Ru i j) t) (erasure i u).
Proof.
    intro H.
    destruct j.
    - simpl. destruct t; auto. apply type_inv_box in H. inversion H.
    - repeat rewrite erasure_prop. auto.
Qed. 

Lemma lam_box_erasure Γ l T i j A B t : 
    Γ ⊢< l > t : T ->
    erasure (Ru i j) (lam i j A B t) = lam_box (erasure j t).
Proof.
    intro H.
    destruct j.
    - simpl. destruct t; auto. apply type_inv_box in H. inversion H.
    - repeat rewrite erasure_prop. auto.
Qed. 


Lemma aux_subst_commute A l x Γ T : 
    Γ ⊢< l > A : T ->
    erasure l (A <[ succ (var x) .: ↑ >> (↑ >> var)]) = (erasure l A) <[ succ (var x) .: ↑ >> (↑ >> var)].
Proof.
    intro H.
    setoid_rewrite (erasure_subst_commutes _ _ _ _ _ _ ((fun _ => ty 0) ;; (ty 0))).
    setoid_rewrite erasure_cons. reflexivity. eauto. 
    simpl.
    assert (((λ _ : nat, ty 0);; ty 0) ~ fun _ => ty 0).
    intro. destruct a; auto.
    setoid_rewrite H0. 
    apply refines_all.
Qed.

Theorem sound : 
    (forall Γ l M T t, Γ ⊢< l > M ⇒ T ↣ t -> 
        forall Γ' 
        (erased_Γ'_eq : erase_ctx Γ' = Γ)
        (Γ'Wf : ⊢ Γ'),
        exists T' t', Γ' ⊢< l > t' : T' /\ erasure l t' = t /\ erasure (Ax l) T' = T
    ) /\ (
    forall Γ l M T t, Γ ⊢< l > M ⇐ T ↣ t -> 
        forall Γ' T'
        (erased_Γ'_eq : erase_ctx Γ' = Γ)
        (erased_T'_eq : erasure (Ax l) T' = T)
        (T'Wt : Γ' ⊢< Ax l > T' : Sort l),
        exists t', Γ' ⊢< l > t' : T' /\ erasure l t' = t
    ).
Proof.
    apply infer_check_mutind; intros; try rewrite <- erased_Γ'_eq in *; clear Γ erased_Γ'_eq.
  
    (* case var *)
    - apply var_in_erased_ctx in e as (A' & H1 & H2). eexists. eexists. repeat split. 
      eapply type_var; eauto. destruct l; auto. rewrite H1. apply erasure_rename_commute. 
  
    (* case sort *)
    - eexists. exists (Sort l). split; eauto using type_sort.
  
    (* case Pi *)
    - (* applying the ih to A *)
      edestruct H as (TA & A' & A'_Wt & erased_A'_eq & erased_TA_eq); eauto.
      dependent destruction erased_A'_eq. dependent destruction erased_TA_eq.
      eapply reduce_to_sort in A'_Wt as (A'_Wt & _); eauto.
      eapply type_conv in A'_Wt; eauto.
      
      (* applying the ih to B *)
      edestruct (H0 (Γ' ,, (i, A'))) as (TB & B' & B'_Wt & erased_B'_eq & erased_TB_eq). 
      all: (eauto using ctx_cons, conv_sort).
      dependent destruction erased_B'_eq. dependent destruction erased_TB_eq.
      eapply reduce_to_sort in B'_Wt as (B'_Wt & _); eauto.

      exists (Sort (Ru i j)). exists (Pi i j A' B').
      repeat split. auto using type_pi.

    (* case app *)
    - (* applying the ih to t *)
      edestruct H as (A' & t' & t'_Wt & erasure_t'_eq & erasure_A'_eq); eauto.
      dependent destruction erasure_t'_eq. dependent destruction erasure_A'_eq.
      eapply reduce_to_pi in t'_Wt as (A0 & B0 & A_eq & B_eq & t'_Wt & l_eq); eauto.
      dependent destruction A_eq. dependent destruction B_eq. dependent destruction l_eq.
      apply validity_ty_ty in t'_Wt as PiA0B0_Wt. 
      apply type_inv_pi' in PiA0B0_Wt as (_ & A0_Wt & B0_Wt & _ & _).

      (* applying the ih to u *)
      edestruct H0 as (u' & u'_Wt & erasure_u'_eq); eauto.
      dependent destruction erasure_u'_eq.

      exists (B0 <[ u' .. ]). exists (app i j A0 B0 t' u').
      repeat split; eauto using type_app.
      destruct j. 
        + eapply app_box_erasure. eauto.
        + simpl. rewrite erasure_prop. auto.
        + eapply erasure_subst_1_commutes; eauto.
    
    (* case Nat *)
    - eexists (Sort (ty 0)). eexists Nat. split; eauto using type_nat.

    (* case zero *)
    - eexists Nat. eexists zero. split; eauto using type_zero.

    (* case succ *)
    - (* applying the ih to t *)
      edestruct H as (_Nat & t' & t'_Wt & erasure_t'_eq & erasure_Nat_eq); eauto.
      dependent destruction erasure_t'_eq. dependent destruction erasure_Nat_eq.
      eapply reduce_to_nat in t'_Wt as (t'_Wt & l_eq_0); eauto.
      dependent destruction l_eq_0.
      exists Nat. exists (succ t'). 
      repeat split; eauto using type_succ.

    (* case rec *)  
    - (* applying the ih to P *)
      edestruct (H (Γ' ,, (ty 0, Nat))) as (_sort & P' & P'_Wt & erased_P'_eq & erased_sort_eq); 
      eauto using ctx_cons, type_nat.
      dependent destruction erased_P'_eq. dependent destruction erased_sort_eq.
      eapply reduce_to_sort in P'_Wt as (P'_Wt & l'_eq); eauto. dependent destruction l'_eq.
      
      (* applying the ih to p_zero *)
      edestruct (H0 Γ' (P' <[ zero..])) as (p_zero' & p_zero'_Wt & erasure_eq); eauto.
      eapply (erasure_subst_1_commutes _ (ty 0)); eauto.
      eapply subst_ty'; eauto using aux_subst_1, type_zero.
      dependent destruction erasure_eq.

      (* applying the ih to p_succ *)
      edestruct (H1 (Γ' ,, (ty 0, Nat) ,, (l, P')) (P' <[ succ (var 1) .: ↑ >> (↑ >> var)])) 
        as (p_succ' & p_succ'_Wt & erasure_eq); eauto.
      eapply aux_subst_commute; eauto.
      eapply subst_ty'; eauto using aux_subst_2.
      dependent destruction erasure_eq.
      
      (* applying the ih to k *)
      edestruct (H2 Γ' Nat) as (k' & k'_Wt & erasure_eq); eauto using type_nat.
      dependent destruction erasure_eq.

      exists (P' <[ k' ..]). exists (rec l P' p_zero' p_succ' k').
      repeat split.
      auto using type_rec.
      eapply erasure_subst_1_commutes; eauto.
      
    (* case annotation *)
    - (* applying the ih to T *)
      edestruct H as (_sort & T' & T'_Wt & erasure_T'_eq & erasure_sort_eq); eauto.
      dependent destruction erasure_T'_eq. dependent destruction erasure_sort_eq.
      eapply reduce_to_sort in T'_Wt as (T'_Wt & l_eq); eauto.
      dependent destruction l_eq.

      (* applying the ih to t *)
      edestruct H0 as (t' & t'_Wt & erasure_t'_eq); eauto.
      
    (* case conv *)
    - dependent destruction erased_T'_eq. 

      (* applying the ih to t *)
      edestruct H as (V' & t' & t'_Wt & erasure_t'_eq & erasure_V'_eq); eauto using validity_ty_ctx.
      dependent destruction erasure_t'_eq. dependent destruction erasure_V'_eq.
      eapply validity_ty_ty in t'_Wt as V'_Wt.
      dependent destruction e.
      assert (Γ' ⊢<Ax l > T'0 ≡ V' : Sort l) by (eapply convcheck_sound; eauto).
      exists t'. split; eauto using type_conv, conv_sym.

    (* case lam *)
    - (* we first derive that T' is convertible to Pi A' B', 
         and that A' B' are well-typed *)
      dependent destruction erased_T'_eq. 
      eapply reduce_to_pi' in T'Wt as (A' & B' & A_eq & B_eq & T'_eq & l_eq); eauto.
      dependent destruction A_eq. dependent destruction B_eq. dependent destruction l_eq.
      apply validity_conv_right in T'_eq as Pi_Wt.
      apply type_inv_pi' in Pi_Wt as (_ & A'_Wt & B'_Wt & _).

      (* applying the ih to t *)
      edestruct H as (t' & t'_Wt & erased_t'_eq); eauto. 
      unfold erase_ctx. reflexivity.
      dependent destruction erased_t'_eq.

      exists (lam i j A' B' t'). split; eauto using type_lam, type_conv, conv_sym, lam_box_erasure.      
Qed.


Corollary infer_sound Γ l M t T :
    ⊢ Γ -> 
    (erase_ctx Γ) ⊢< l > M ⇒ T ↣ t -> 
    exists T' t', Γ ⊢< l > t' : T' /\ erasure l t' = t /\ erasure (Ax l) T' = T.
Proof.
    intros. eapply (proj1 sound); eauto.
Qed.


Corollary check_sound Γ l M t T :
    Γ ⊢< Ax l > T : Sort l -> 
    (erase_ctx Γ) ⊢< l > M ⇐ (erasure (Ax l) T) ↣ t -> 
    exists t', Γ ⊢< l > t' : T /\ erasure l t' = t.
Proof.
    intros. eapply (proj2 sound); eauto.
Qed.