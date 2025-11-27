
From Stdlib Require Import Utf8 List Arith Bool Lia Wellfounded.Inverse_Image Wellfounded.Inclusion.
From TypedConfluence
Require Import core unscoped Ast SubstNotations RAsimpl AST_rasimpl.
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
| clam' : cterm -> cterm -> cterm

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
    Γ ∋< l > x : A →
    Γ ⊢< l > cvar x ⇒ A ↣ box_if_prop l (var x)

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

| infer_lam Γ l i j MA Mt UA A B t :
    Γ ⊢< l > MA ⇒ UA ↣ A ->
    UA -->> Sort i ->
    Γ ,, (i , A) ⊢< j > Mt ⇒ B ↣ t ->
    Γ ⊢< Ru i j > clam' MA Mt ⇒ Pi i j A B ↣ lam_box t

| infer_Nat Γ :
    Γ ⊢< ty 1 > cNat ⇒ Sort (ty 0) ↣ Nat

| infer_zero Γ :
    Γ ⊢< ty 0 > czero ⇒ Nat ↣ zero

| infer_succ Γ Mt t :
    Γ ⊢< ty 0 > Mt ⇐ Nat ↣ t ->
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
    erase_ctx Γ ∋< l > x : A →
    ∃ A', A = erasure (Ax l) A' ∧ Γ ∋< l > x : A'.
Proof.
    intro H.
    rename Γ into Δ. remember (erase_ctx Δ) as Γ eqn: e.
    induction H as [| Γ i j A B x h ih] in Δ, e |- *.
    - destruct Δ. 1: discriminate.
      cbn in e. inversion e. subst.
      rewrite <- erasure_rename_commute.
      eexists. split. 1: reflexivity.
      destruct p. constructor.
    - destruct Δ. 1: discriminate.
      cbn in e. inversion e. subst.
      specialize (ih _ eq_refl). destruct ih as (A' & -> & hx).
      rewrite <- erasure_rename_commute.
      eexists. split. 1: reflexivity.
      destruct p. constructor. assumption.
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
    apply type_inv_sort' in Sort_wt as (l_eq_0 & _).
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
    apply type_inv_pi' in pi_wt as (_ & _ & l_eq_ru & _).
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
    apply type_inv_pi' in pi_wt as (_ & _ & l_eq_ru & _).
    apply Ax_inj in l_eq_ru. dependent destruction l_eq_ru.
    exists _pi1. exists _pi2.
    split; eauto using type_conv.
Qed.
(*

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
Qed. *)

(* Lemma app_box_app Γ l A i t u :
    Γ ⊢< l > t : A ->
    app_box (erasure (ty i) t) u = app prop prop box box (erasure (ty i) t) u.
Proof.
    intro Wt.
    destruct t; auto.
    apply type_inv_box' in Wt. inversion Wt.
Qed. *)

Lemma app_box_erasure Γ l T i j A B t u :
    Γ ⊢< l > t : T ->
    erasure j (app i j A B t u) = app_box (erasure (Ru i j) t) (erasure i u).
Proof.
    intro H.
    destruct j.
    - simpl. destruct t; auto. apply type_inv_box' in H. inversion H.
    - repeat rewrite erasure_prop. auto.
Qed.

Lemma lam_box_erasure Γ l T i j A B t :
    Γ ⊢< l > t : T ->
    erasure (Ru i j) (lam i j A B t) = lam_box (erasure j t).
Proof.
    intro H.
    destruct j.
    - simpl. destruct t; auto. apply type_inv_box' in H. inversion H.
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
    - apply var_in_erased_ctx in v as (A' & -> & H2).
      eexists _,_. repeat split.
      + eapply type_var; eauto.
      + destruct l; auto.

    (* case sort *)
    - eexists. exists (Sort l). split; eauto using type_sort.

    (* case Pi *)
    - (* applying the ih to A *)
      edestruct H as (TA & A' & A'_Wt & erased_A'_eq & erased_TA_eq); eauto.
      dependent destruction erased_A'_eq. dependent destruction erased_TA_eq.
      eapply reduce_to_sort in A'_Wt as (A'_Wt & _); eauto.

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
      apply type_inv_pi' in PiA0B0_Wt as (A0_Wt & B0_Wt & _ & _).

      (* applying the ih to u *)
      edestruct H0 as (u' & u'_Wt & erasure_u'_eq); eauto.
      dependent destruction erasure_u'_eq.

      exists (B0 <[ u' .. ]). exists (app i j A0 B0 t' u').
      repeat split; eauto using type_app.
      destruct j.
        + eapply app_box_erasure. eauto.
        + simpl. rewrite erasure_prop. auto.
        + eapply erasure_subst_1_commutes; eauto.

    - edestruct H as (TA & A' & A'_Wt & erased_A'_eq & erased_TA_eq); eauto.
      dependent destruction erased_A'_eq. dependent destruction erased_TA_eq.
      eapply reduce_to_sort in A'_Wt as (A'_Wt & l_eq); eauto.
      dependent destruction l_eq.

      edestruct (H0 (Γ' ,, (i, A'))) as (T & t' & t'_Wt & erased_t'_eq & erased_T_eq); eauto using ctx_cons.
      dependent destruction erased_t'_eq. dependent destruction erased_T_eq.

      exists (Pi i j A' T). exists (lam i j A' T t').
      repeat split; eauto using type_lam, validity_ty_ty, lam_box_erasure.

    (* case Nat *)
    - eexists (Sort (ty 0)). eexists Nat. split; eauto using type_nat.

    (* case zero *)
    - eexists Nat. eexists zero. split; eauto using type_zero.

    (* case succ *)
    - (* applying the ih to t *)
      edestruct (H Γ' Nat) as (t' & t'_Wt & erasure_t'_eq); eauto using type_nat.
      dependent destruction erasure_t'_eq.
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
      eapply subst_ty; eauto using subst_one, type_zero.
      dependent destruction erasure_eq.

      (* applying the ih to p_succ *)
      edestruct (H1 (Γ' ,, (ty 0, Nat) ,, (l, P')) (P' <[ succ (var 1) .: ↑ >> (↑ >> var)]))
        as (p_succ' & p_succ'_Wt & erasure_eq); eauto.
      eapply aux_subst_commute; eauto.
      eapply subst_ty; eauto using aux_subst_2, ctx_typing, type_nat.
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
      apply type_inv_pi' in Pi_Wt as (A'_Wt & B'_Wt & _).

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

Definition wt_is_wn :=
    forall Γ l t A,
    Γ ⊢< l > t : A ->
    exists u, (erasure l t) -->> u /\ nf u.


Lemma gen_red_to_sort Γ i A :
    wt_is_wn ->
    Γ ⊢< Ax (Ax i) > Sort i ≡ A : Sort (Ax i) ->
    erasure (Ax (Ax i)) A -->> Sort i.
Proof.
    intros wt_is_wn sort_eq_A.
    apply validity_conv_right in sort_eq_A as A_Wt.
    pose proof A_Wt as A_Wt'.
    apply wt_is_wn in A_Wt as (B' & erasure_A_red & B'_nf).
    eapply subject_reduction_redd in A_Wt' as (B & A_eq_B & erasure_B); eauto.
    dependent destruction erasure_B.
    assert (Γ ⊢< Ax (Ax i) > Sort i ≡ B : Sort (Ax i)) as sort_eq_B by eauto using conv_trans.
    apply CR in sort_eq_B as (_sort & sort_red_sort & B_red_sort).
    eapply sort_redd in sort_red_sort.
    dependent destruction sort_red_sort.
    eapply ortho_redd_to_red in B_red_sort; eauto.
    rewrite B_red_sort in erasure_A_red.
    auto.
Qed.

Lemma gen_red_to_pi Γ i j A B T :
    wt_is_wn ->
    Γ ⊢< Ax (Ru i j) > Pi i j A B ≡ T : Sort (Ru i j) ->
    exists A' B',
    Γ ⊢< Ax i > A ≡ A' : Sort i /\
    Γ ,, (i, A) ⊢< Ax j > B ≡ B' : Sort j /\
    erasure (Ax (Ru i j)) T -->> Pi i j (erasure (Ax i) A') (erasure (Ax j) B').
Proof.
    intros wt_is_wn pi_eq_T.
    apply validity_conv_right in pi_eq_T as T_Wt.
    pose proof T_Wt as T_Wt'.
    apply wt_is_wn in T_Wt as (U' & erasure_T_red & U'_nf).
    eapply subject_reduction_redd in T_Wt' as (U & T_eq_U & erasure_U); eauto.
    dependent destruction erasure_U.
    assert (Γ ⊢< Ax (Ru i j) > Pi i j A B ≡ U : Sort (Ru i j)) as pi_eq_U by eauto using conv_trans.
    apply CR in pi_eq_U as (_pi & pi_red_pi & U_red_pi).
    eapply pi_redd in pi_red_pi as (A' & B' & pi_eq & A_red_A' & B_red_B').
    dependent destruction pi_eq.
    apply redd_to_conv in A_red_A' as A_eq_A'.
    apply redd_to_conv in B_red_B' as B_eq_B'.
    eapply ortho_redd_to_red in U_red_pi; eauto.
    rewrite U_red_pi in erasure_T_red.
    exists A'. exists B'. split; eauto.
Qed.





Inductive label : Type := | agda | rocq.

Inductive CTerm : label -> cterm -> Prop :=

(* in agda we have non-annotated abstractions and type ascriptions *)
| clam_ M : CTerm agda M -> CTerm agda (clam M)
| cann_ M MA : CTerm agda M -> CTerm agda MA -> CTerm agda (cann M MA)

(* in rocq we have annotated abstractions and no ascriptions *)
| clam'_ MA M : CTerm rocq MA -> CTerm rocq M -> CTerm rocq (clam' MA M)

(* all the rest is the same *)
| cvar_ h n : CTerm h (cvar n)
| cSort_ h i : CTerm h (cSort i)
| cPi_ h MA MB : CTerm h MA -> CTerm h MB -> CTerm h (cPi MA MB)
| capp_ h M N : CTerm h M -> CTerm h N -> CTerm h (capp M N)
| cNat_ h : CTerm h cNat
| czero_ h : CTerm h czero
| csucc_ h M : CTerm h M -> CTerm h (csucc M)
| crec_ h MP Mp_zero Mp_succ Mk : CTerm h MP -> CTerm h Mp_zero ->
    CTerm h Mp_succ -> CTerm h Mk -> CTerm h (crec MP Mp_zero Mp_succ Mk).


Lemma completeness_aux Γ l t T Δ h :
    wt_is_wn ->
    Γ ⊢< l > t : T ->
    ⊢ Γ ≡ Δ ->
    (exists M U,
        (erase_ctx Δ) ⊢< l > M ⇒ (erasure (Ax l) U) ↣ (erasure l t)
        /\ Γ ⊢< Ax l > T ≡ U : Sort l
        /\ CTerm h M)
    ->
    (forall U,
        Γ ⊢< Ax l > T ≡ U : Sort l ->
        exists M, (erase_ctx Δ) ⊢< l > M ⇐ (erasure (Ax l) U) ↣ (erasure l t) /\ CTerm h M)
    /\
    (exists M U,
        (erase_ctx Δ) ⊢< l > M ⇒ (erasure (Ax l) U) ↣ (erasure l t)
        /\ Γ ⊢< Ax l > T ≡ U : Sort l
        /\ CTerm h M).
Proof.
    intros wt_is_wn tWt Γ_eq_Δ H.
    split; intros; auto.
    edestruct H as (M & V & M_infer & T_eq_V & C); eauto.
    assert (Γ ⊢< Ax l > V ≡ U : Sort l) as V_eq_U by eauto using conv_sym, conv_trans.
    apply validity_conv_left in V_eq_U as V_wt.
    apply validity_conv_right in V_eq_U as U_wt.
    apply wt_is_wn in V_wt as (V' & V_redd_V' & nf_V').
    apply wt_is_wn in U_wt as (U' & U_redd_U' & nf_U').
    exists M. split; eauto.
    eapply check_conv; eauto.
    eapply convcheck_complete; eauto.
Qed.


(* we separate the case in the proof for pi, because we reuse it in the
  case for lam, when constructing the type annotation needed for inference *)
Lemma completeness_pi Γ i j A B h :
    wt_is_wn ->
    Γ ⊢< Ax i > A : Sort i ->
    Γ,, (i, A) ⊢< Ax j > B : Sort j ->
    Γ ⊢< Ax (Ru i j) > Pi i j A B : Sort (Ru i j) ->
    (∀ Δ : ctx, ⊢ Γ ≡ Δ →
        ∃ (M : cterm) (U : term),
            erase_ctx Δ ⊢< Ax i > M ⇒ erasure (Ax (Ax i)) U ↣ erasure (Ax i) A ∧
            Γ ⊢< Ax (Ax i) > Sort i ≡ U : Sort (Ax i) ∧ CTerm h M) ->
    (∀ Δ : ctx, ⊢ Γ,, (i, A) ≡ Δ →
        ∃ (M : cterm) (U : term),
            erase_ctx Δ ⊢< Ax j > M ⇒ erasure (Ax (Ax j)) U ↣ erasure (Ax j) B ∧
            Γ,, (i, A) ⊢< Ax (Ax j) > Sort j ≡ U : Sort (Ax j)  ∧ CTerm h M) ->
    forall Δ, ⊢ Γ ≡ Δ ->
    ∃ (M : cterm) (U : term),
        erase_ctx Δ ⊢< Ax (Ru i j) > M ⇒ erasure (Ax (Ax (Ru i j))) U ↣ erasure (Ax (Ru i j)) (Pi i j A B) ∧
        Γ ⊢< Ax (Ax (Ru i j)) > Sort (Ru i j) ≡ U : Sort (Ax (Ru i j)) ∧
        CTerm h M.
Proof.
    intros wt_is_wn A_Wt B_Wt Pi_Wt HA HB Δ Γ_eq_Δ.
    edestruct HA as (MA & UA & MA_infer & sort_eq_UA & CA); eauto.
    eapply gen_red_to_sort in sort_eq_UA; eauto.

    edestruct HB as (MB & UB & MB_infer & sort_eq_UB & CB); eauto using conv_ccons, conv_refl.
    eapply gen_red_to_sort in sort_eq_UB; eauto.

    exists (cPi MA MB). exists (Sort (Ru i j)).
    repeat split; eauto using CTerm. eapply infer_pi; eauto. eauto using validity_ty_ty, conv_refl.
Qed.

Lemma varty_erase Γ l x A :
    Γ ∋< l > x : A →
    erase_ctx Γ ∋< l > x : erasure (Ax l) A.
Proof.
    intros h. induction h.
    - cbn. rewrite erasure_rename_commute. constructor.
    - cbn. rewrite erasure_rename_commute. constructor. eauto.
Qed.

Theorem completeness Γ l t T Δ h :
    wt_is_wn ->
    Γ ⊢< l > t : T ->
    ⊢ Γ ≡ Δ ->
    (forall U,
        Γ ⊢< Ax l > T ≡ U : Sort l ->
        exists M, (erase_ctx Δ) ⊢< l > M ⇐ (erasure (Ax l) U) ↣ (erasure l t) /\ CTerm h M)
    /\
    (exists M U,
        (erase_ctx Δ) ⊢< l > M ⇒ (erasure (Ax l) U) ↣ (erasure l t)
        /\ Γ ⊢< Ax l > T ≡ U : Sort l
        /\ CTerm h M).
Proof.
    intros wt_is_wn Wt.
    pose proof Wt as Wt'.
    generalize Δ. clear Δ.
    induction Wt;intros.

    (* in most cases, we show only the inference and then derive checking automatically *)
    1,2,3,5,6,7,8,9: (eapply completeness_aux; eauto).

    (* case var *)
    - eapply conv_ctx_var in H0 as (B & nth_x & conv); eauto.
      exists (cvar x). eexists.
      repeat split; eauto using CTerm.
      + eapply infer_var. apply varty_erase. assumption.

    (* case sort *)
    - exists (cSort l). exists (Sort (Ax l)).
      split; eauto using CTerm, conv_refl, validity_ty_ty, infer_Sort.

    (* case pi *)
    - eapply completeness_pi; eauto. apply IHWt1; eauto. apply IHWt2; eauto.

    (* case app *)
    - edestruct IHWt3 as (_ & Mt & UA & Mr_infer & pi_eq_UA & Ct); eauto.
      eapply gen_red_to_pi in pi_eq_UA as (A' & B' & A_eq_A' & B_eq_B' & erasure_UA_red); eauto.

      edestruct IHWt4 as ((Mu & Mu_check & Cu) & _); eauto.

      exists (capp Mt Mu). eexists (B' <[ u ..]). repeat split; eauto using CTerm.
      + erewrite app_box_erasure; eauto.
        erewrite erasure_subst_1_commutes; eauto using validity_conv_right.
        eapply infer_app; eauto.
      + eauto using subst_conv, subst_one, validity_conv_ctx, refl_subst.

    (* case nat *)
    - exists cNat. exists (Sort (ty 0)).
      split; eauto using conv_refl, validity_ty_ty, infer_Nat, CTerm.

    (* case zero *)
    - exists czero. exists Nat.
      split; eauto using conv_refl, validity_ty_ty, infer_zero, CTerm.

    (* case succ *)
    - edestruct IHWt as ((Mt & Mt_check & Ct) & _); eauto using validity_ty_ty, conv_refl.
      exists (csucc Mt). exists Nat.
      split; eauto using conv_refl, validity_ty_ty, infer_succ, CTerm.

    (* case rec *)
    - edestruct IHWt1 as (_ & MP & U & MP_infer & sort_eq_U & CP); eauto using conv_ccons, conv_nat, validity_ty_ctx.
      eapply gen_red_to_sort in sort_eq_U; eauto.

      edestruct IHWt2 as ((Mp_zero & Mp_zero_check & Cp_zero) & _); eauto using conv_refl, validity_ty_ty.

      edestruct IHWt3 as ((Mp_succ & Mp_succ_check & Cp_succ) & _); eauto 7 using conv_ccons, conv_nat, conv_refl, validity_ty_ty.

      edestruct IHWt4 as ((Mt & Mt_check & Ct) & _); eauto using conv_refl, validity_ty_ty.

      exists (crec MP Mp_zero Mp_succ Mt). exists (P <[ t ..]).
      split; eauto using conv_refl, validity_ty_ty, CTerm.
      erewrite erasure_subst_1_commutes; eauto.
      eapply infer_rec; eauto; fold erasure.
      + erewrite erasure_subst_1_commutes in Mp_zero_check; eauto. eauto.
      + erewrite aux_subst_commute in Mp_succ_check; eauto.

    (* case lam *)
    - destruct h.
            (* subcase agda: we use a type ascription to construct an inferring lambda  *)
        +   assert (∀ U : term, Γ ⊢< Ax (Ru i j) > Pi i j A B ≡ U : Sort (Ru i j) →
                ∃ M : cterm,
                    erase_ctx Δ ⊢< Ru i j > M ⇐ erasure (Ax (Ru i j)) U ↣ erasure (Ru i j) (lam i j A B t)
                    ∧ CTerm agda M)
                as H'.
            { intros.
                eapply gen_red_to_pi in H0 as (A' & B' & A_eq_A' & B_eq_B' & U_red_pi); eauto.
                edestruct IHWt3 as ((Mt & Mt_check & Ct) & _); eauto using conv_ccons, conv_refl.
                exists (clam Mt). erewrite lam_box_erasure; eauto. split; eauto using CTerm.
                eapply check_lam. apply U_red_pi. eauto. }
            split; eauto.

            assert (∃ (M : cterm) (U : term),
                erase_ctx Δ ⊢< Ax (Ru i j) > M ⇒ erasure (Ax (Ax (Ru i j))) U ↣ erasure (Ax (Ru i j)) (Pi i j A B) ∧
                Γ ⊢< Ax (Ax (Ru i j)) > Sort (Ru i j) ≡ U : Sort (Ax (Ru i j)) /\ CTerm agda M)
                as (Mpi & U & Mpi_infer & sort_eq_U & Cpi).
            { eapply completeness_pi; eauto using validity_ty_ty. apply IHWt1; eauto. apply IHWt2; eauto. }
            eapply gen_red_to_sort in sort_eq_U; eauto.

            edestruct H' as (Mlam & Mlam_checks & Clam); eauto using validity_ty_ty, conv_refl.

            exists (cann Mlam Mpi). exists (Pi i j A B). repeat split; eauto using CTerm.
            ++ eapply infer_ann; eauto.
            ++ eauto using validity_ty_ty, conv_refl.

            (* subcase rocq, we use completeness_aux and only show inference, using an annotated lambda *)
        +   apply completeness_aux; eauto.
            edestruct IHWt1 as (_ & MA & UA & MA_infer & sort_eq_UA & CA); eauto.
            eapply gen_red_to_sort in sort_eq_UA; eauto.

            edestruct IHWt3 as (_ & Mt & B' & Mt_infer & B_eq_B' & CM); eauto using conv_ccons, conv_refl.

            exists (clam' MA Mt). exists (Pi i j A B').
            repeat split; eauto using CTerm.
            ++ erewrite lam_box_erasure; eauto. eapply infer_lam; eauto.
            ++ eauto using conv_pi, conv_refl.

    (* case conv *)
    - eapply IHWt in H0 as (IH_check & IH_infer); eauto. split; intros.
      + assert (Γ ⊢< Ax l > A ≡ U : Sort l) as A_eq_U by eauto using conv_sym, conv_trans.
        eapply IH_check in A_eq_U as (M & M_check & CM). eauto.
      + destruct IH_infer as (M & U & M_infer & B_eq_U & CM).
        assert (Γ ⊢< Ax l > A ≡ U : Sort l) as A_eq_U by eauto using conv_sym, conv_trans.
        exists M. exists U. split; eauto using conv_sym, conv_trans.
Qed.

Corollary completeness_check Γ l t T h :
    wt_is_wn -> Γ ⊢< l > t : T ->
    exists M, (erase_ctx Γ) ⊢< l > M ⇐ (erasure (Ax l) T) ↣ (erasure l t)  /\ CTerm h M.
Proof.
    intros. pose proof H0 as Wt.
    eapply completeness in Wt as (case_check & case_infer);
    eauto using refl_ctx, validity_ty_ctx.
    eapply case_check. eauto using validity_ty_ty, conv_refl.
Qed.

Corollary completeness_infer Γ l t T h :
    wt_is_wn -> Γ ⊢< l > t : T ->
    exists M U, (erase_ctx Γ) ⊢< l > M ⇒ (erasure (Ax l) U) ↣ (erasure l t)
        /\ Γ ⊢< Ax l > T ≡ U : Sort l  /\ CTerm h M.
Proof.
    intros. pose proof H0 as Wt.
    eapply completeness in Wt as (case_check & case_infer);
    eauto using refl_ctx, validity_ty_ctx.
Qed.


Print Assumptions completeness_infer.

Definition Decidable (P : Prop) := sum P (not P).

Theorem decidable Γ M :
    wt_is_wn ->
    (⊢ Γ -> Decidable (exists l T t, Γ ⊢< l > M ⇒ T ↣ t))
    *
    (forall T l, Γ ⊢< Ax l > T : Sort l ->
        Decidable (exists t, Γ ⊢< l > M ⇐ T ↣ t)).
Proof.
Admitted.
