
From Stdlib Require Import Utf8 List Arith Bool Lia Wellfounded.Inverse_Image Wellfounded.Inclusion.
From TypedConfluence
Require Import core unscoped Ast SubstNotations RAsimpl AST_rasimpl.
From TypedConfluence Require Import Util BasicAST Contexts Typing BasicMetaTheory Confluence ConversionChecking.
From Stdlib Require Import Setoid Morphisms Relation_Definitions.
(* Require Import Stdlib.Program.Equality. *)
Require Import Equations.Prop.DepElim.
From Equations Require Import Equations.
Import CombineNotations.


Inductive cterm : Type :=
| cann : cterm -> cterm -> cterm
| cvar : nat -> cterm
| cSort : level -> cterm

| cPi : cterm -> cterm -> cterm
| capp : cterm -> cterm -> cterm
| clam : cterm -> cterm
| clam' : cterm -> cterm -> cterm

| cSigma : cterm -> cterm -> cterm 
| cpair : cterm -> cterm -> cterm
| cpair' : cterm -> cterm -> cterm -> cterm
| cpi1 : cterm -> cterm
| cpi2 : cterm -> cterm

| cNat : cterm
| czero : cterm
| csucc : cterm -> cterm
| crec : cterm -> cterm -> cterm -> cterm -> cterm

| cEq : cterm -> cterm -> cterm -> cterm 
| cJ : cterm -> cterm -> cterm -> cterm -> cterm -> cterm -> cterm

| cLift : cterm -> cterm 
| clift : cterm -> cterm
| clower : cterm -> cterm

| ccast : cterm -> cterm -> cterm 
| cinjpi1 : cterm -> cterm 
| cinjpi2 : cterm -> cterm -> cterm.

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


Definition J_box l i A a P p b e :=
    match i with
    | prop => box
    | _ => J l i A a P p b e
    end.

Definition lower_box i a :=
    match i with 
    | prop => box 
    | _ => lower prop box a 
    end.

Definition cast_box i A B a := 
    match i with 
    | prop => box
    | _ => cast i A B box a 
    end.

Definition pi1_box t := pi1 prop prop box box t.

Definition pi2_box t := pi2 prop prop box box t.

Definition pair_box t u := pair prop prop box box t u.

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

| infer_sigma Γ i' j' n m T U MA MB A B :
    Γ ⊢< i' > MA ⇒ T ↣ A ->
    T -->> Sort (ty n) ->
    Γ ,, (ty n , A) ⊢< Ax j' > MB ⇒ U ↣ B ->
    U -->> Sort (ty m) ->
    Γ ⊢< Ax (ty (max n m)) > cSigma MA MB ⇒ Sort (ty (max n m)) ↣ Sigma (ty n) (ty m) A B

| infer_pi1 Γ l Mt T t A B n m :
    Γ ⊢< l > Mt ⇒ T ↣ t ->
    T -->> Sigma (ty n) (ty m) A B -> 
    Γ ⊢< ty n > cpi1 Mt ⇒ A ↣ pi1_box t

| infer_pi2 Γ l Mt T t A B n m :
    Γ ⊢< l > Mt ⇒ T ↣ t ->
    T -->> Sigma (ty n) (ty m) A B -> 
    Γ ⊢< ty m > cpi2 Mt ⇒ B <[(pi1_box t)..] ↣ pi2_box t

| infer_pair Γ l n m Mt A t T B Mu MB u :
    Γ ⊢< ty n > Mt ⇒ A ↣ t ->
    Γ ,, (ty n , A) ⊢< l > MB ⇒ T ↣ B ->
    T -->> Sort (ty m) ->
    Γ ⊢< ty m > Mu ⇐ B <[t..] ↣ u ->
    Γ ⊢< ty (max n m) > cpair' Mt MB Mu ⇒ Sigma (ty n) (ty m) A B ↣ pair_box t u

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

| infer_eq Γ i MA T A Ma a Mb b : 
    Γ ⊢< Ax i > MA ⇒ T ↣ A ->
    T -->> Sort i ->
    Γ ⊢< i > Ma ⇐ A ↣ a ->
    Γ ⊢< i > Mb ⇐ A ↣ b ->
    Γ ⊢< Ax prop > cEq MA Ma Mb ⇒ Sort prop ↣ Eq i A a b

| infer_J Γ l MA T A Ma a i MP U P Mp p Mb b Me e :
    Γ ⊢< Ax l > MA ⇒ T ↣ A ->
    T -->> Sort l ->
    Γ ⊢< l > Ma ⇐ A ↣ a ->
    Γ ,, (l, A) ⊢< Ax i > MP ⇒ U ↣ P ->
    U -->> Sort i ->
    Γ ⊢< i > Mp ⇐ P<[a..] ↣ p ->
    Γ ⊢< l > Mb ⇐ A ↣ b ->
    Γ ⊢< prop > Me ⇐ Eq l A a b ↣ e ->
    Γ ⊢< i > cJ MA Ma MP Mp Mb Me ⇒ P <[b..] ↣ J_box l i A a P p b e

| infer_Lift Γ i MA T A :
    Γ ⊢< Ax i > MA ⇒ T ↣ A ->
    T -->> Sort i ->
    Γ ⊢< Ax (Ax i) > cLift MA ⇒ Sort (Ax i) ↣ Lift i A

| infer_lower Γ i Ma T a A :
    Γ ⊢< Ax i > Ma ⇒ T ↣ a ->
    T -->> Lift i A ->
    Γ ⊢< i > clower Ma ⇒ A ↣ lower_box i a

| infer_lift Γ i Ma a A :
    Γ ⊢< i > Ma ⇒ A ↣ a ->
    Γ ⊢< Ax i > clift Ma ⇒ Lift i A ↣ lift prop box a

| infer_cast Γ Me T e i A B Ma a :
    Γ ⊢< prop > Me ⇒ T ↣ e ->
    T -->> Eq (Ax i) (Sort i) A B ->
    Γ ⊢< i > Ma ⇐ A ↣ a ->
    Γ ⊢< i > ccast Me Ma ⇒ B ↣ cast_box i A B a

| infer_injpi1 Γ Me T e i n A1 B1 A2 B2 :
    Γ ⊢< prop > Me ⇒ T ↣ e ->
    T -->> Eq (Ax (Ru i (ty n))) (Sort (Ru i (ty n))) 
            (Pi i (ty n) A1 B1) (Pi i (ty n) A2 B2) ->
    Γ ⊢< prop > cinjpi1 Me ⇒ Eq (Ax i) (Sort i) A2 A1 ↣ box

| infer_injpi2 Γ Me T e i n A1 B1 A2 B2 Ma a2 :
    Γ ⊢< prop > Me ⇒ T ↣ e ->
    T -->> Eq (Ax (Ru i (ty n))) (Sort (Ru i (ty n))) 
            (Pi i (ty n) A1 B1) (Pi i (ty n) A2 B2) ->
    Γ ⊢< i > Ma ⇐ A2 ↣ a2 ->
    let a1 := cast_box i A2 A1 a2 in
    Γ ⊢< prop > cinjpi2 Me Ma ⇒ Eq (Ax (ty n)) (Sort (ty n)) (B1<[a1..]) (B2 <[a2..]) ↣ box

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

| check_pair Γ n m Mt A t T B Mu u :
    T -->> Sigma (ty n) (ty m) A B ->
    Γ ⊢< ty n > Mt ⇐ A ↣ t ->
    Γ ⊢< ty m > Mu ⇐ B <[t..] ↣ u ->
    Γ ⊢< ty (max n m) > cpair Mt Mu ⇐ T ↣ pair_box t u    

| check_lift Γ l i Ma a T A :
    T -->> Lift i A ->
    Γ ⊢< i > Ma ⇐ A ↣ a ->
    Γ ⊢< l > clift Ma ⇐ T ↣ lift prop box a

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
    apply type_inv in Sort_wt. dependent destruction Sort_wt. 
    apply Ax_inj in lvl_eq. subst.
    split; eauto using type_conv.
Qed.

Lemma reduce_to Γ l T U :
    Γ ⊢< Ax l > T : Sort l ->
    erasure (Ax l) T -->> U ->
    match U with 
    | Pi i j A B => 
        exists A' B', 
        A = erasure (Ax i) A' /\
        B = erasure (Ax j) B' /\ 
        Γ ⊢< Ax (Ru i j) > T ≡ Pi i j A' B' : Sort (Ru i j) /\ 
        l = Ru i j
    | Sigma i j A B => 
        exists A' B' n m, 
        i = ty n /\ 
        j = ty m /\
        A = erasure (Ax (ty n)) A' /\
        B = erasure (Ax (ty m)) B' /\ 
        Γ ⊢< Ax (ty (max n m)) > T ≡ Sigma (ty n) (ty m) A' B' : Sort (ty (max n m)) /\ 
        l = ty (max n m)
    | Lift i A =>
        exists A', 
        A = erasure (Ax i) A' /\ 
        Γ ⊢< Ax (Ax i) > T ≡ Lift i A' : Sort (Ax i) /\ 
        l = Ax i
    | Eq i A a b =>
        exists A' a' b',
        A = erasure (Ax i) A' /\
        a = erasure i a' /\
        b = erasure i b' /\
        Γ ⊢< Ax prop > T ≡ Eq i A' a' b' : Sort prop /\
        l = prop
    | _ => True
    end.
Proof.
    intros t_Wt erasure_red.
    eapply subject_reduction_redd in erasure_red as (_ty & TA_eq_ty & erasure_ty_eq_ty) ; eauto using validity_ty_ty.
    destruct U; eauto.

    all:destruct _ty; dependent destruction erasure_ty_eq_ty;
    apply validity_conv_right in TA_eq_ty as ty_wt;
    apply type_inv in ty_wt as temp; dependent destruction temp;
    apply Ax_inj in lvl_eq; subst; repeat eexists; eauto using type_conv.
Qed.


Lemma app_box_erasure Γ T i j A B t u :
    Γ ⊢< Ru i j > t : T ->
    erasure j (app i j A B t u) = app_box (erasure (Ru i j) t) (erasure i u).
Proof.
    intro H.
    destruct j.
    - simpl. destruct t; auto; apply type_inv in H; dependent destruction H; dependent destruction lvl_eq.
    - repeat rewrite erasure_prop. auto.
Qed.

Lemma lam_box_erasure Γ T i j A B t :
    Γ ⊢< j > t : T ->
    erasure (Ru i j) (lam i j A B t) = lam_box (erasure j t).
Proof.
    intro H.
    destruct j.
    - simpl. destruct t; auto; apply type_inv in H; dependent destruction H; dependent destruction lvl_eq.
    - repeat rewrite erasure_prop. auto.
Qed.

(* Lemma cast_box_erasure i A B e t :
    erasure i (cast i A B e t) = cast_box i (erasure (Ax i) A) (erasure (Ax i) B) (erasure i t).
Proof.
    reflexivity.
Qed. *)

Lemma J_box_erasure l i A a P p b e :
    erasure i (J l i A a P p b e) = J_box l i (erasure (Ax l) A) (erasure l a) (erasure (Ax i) P) (erasure i p) (erasure l b) box.
Proof.
    destruct i.
    - simpl. reflexivity.
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
      edestruct H as (TA & A' & A'_Wt & erased_A'_eq & erased_TA_eq); eauto. subst.
      eapply reduce_to_sort in A'_Wt as (A'_Wt & _); eauto.

      (* applying the ih to B *)
      edestruct (H0 (Γ' ,, (i, A'))) as (TB & B' & B'_Wt & erased_B'_eq & erased_TB_eq).
      all: (eauto using ctx_cons, conv_sort). subst.
      eapply reduce_to_sort in B'_Wt as (B'_Wt & _); eauto.

      exists (Sort (Ru i j)). exists (Pi i j A' B').
      repeat split. auto using type_pi.

    (* case app *)
    - (* applying the ih to t *)
      edestruct H as (A' & t' & t'_Wt & erasure_t'_eq & erasure_A'_eq); eauto.
      subst.
      eapply validity_ty_ty in t'_Wt as A'_Wt. 
      eapply reduce_to in r as (A0 & B0 & A_eq & B_eq & T'_eq & l_eq); eauto. subst.
      eapply type_conv in t'_Wt; eauto. clear T'_eq.

      apply validity_ty_ty in t'_Wt as PiA0B0_Wt.
      apply type_inv in PiA0B0_Wt as temp. dependent destruction temp.

      (* applying the ih to u *)
      edestruct H0 as (u' & u'_Wt & erasure_u'_eq); eauto. subst.

      exists (B0 <[ u' .. ]). exists (app i j A0 B0 t' u').
      repeat split; eauto using type_app.
      destruct j.
        + eapply app_box_erasure. eauto.
        + simpl. rewrite erasure_prop. auto.
        + eapply erasure_subst_1_commutes; eauto.

    (* case lam *)
    - edestruct H as (TA & A' & A'_Wt & erased_A'_eq & erased_TA_eq); eauto.
      subst.
      eapply reduce_to_sort in A'_Wt as (A'_Wt & l_eq); eauto. subst.

      edestruct (H0 (Γ' ,, (i, A'))) as (T & t' & t'_Wt & erased_t'_eq & erased_T_eq); eauto using ctx_cons.
      subst.

      exists (Pi i j A' T). exists (lam i j A' T t').
      repeat split; eauto using type_lam, validity_ty_ty, lam_box_erasure.

    (* case Sigma *)
    - (* applying the ih to A *)
      edestruct H as (TA & A' & A'_Wt & erased_A'_eq & erased_TA_eq); eauto. subst.
      eapply reduce_to_sort in A'_Wt as (A'_Wt & lvleq); eauto. subst.

      (* applying the ih to B *)
      edestruct (H0 (Γ' ,, (ty n, A'))) as (TB & B' & B'_Wt & erased_B'_eq & erased_TB_eq).
      all: (eauto using ctx_cons, conv_sort). subst.
      eapply reduce_to_sort in B'_Wt as (B'_Wt & lvl_eq); eauto. 
      eapply Ax_inj in lvl_eq. subst.

      exists (Sort (ty (max n m))). exists (Sigma (ty n) (ty m) A' B').
      repeat split. econstructor; eauto.

    (* case pi1 *)
    - (* applying the ih to t *)
      edestruct H as (A' & t' & t'_Wt & erasure_t'_eq & erasure_A'_eq); eauto.
      subst.
      eapply validity_ty_ty in t'_Wt as A'_Wt. 
      eapply reduce_to in r as (A0 & B0 & n' & m' & eq1 & eq2 & A_eq & B_eq & T'_eq & l_eq); eauto.
      ty_inj_tac. subst.
      eapply type_conv in t'_Wt; eauto. clear T'_eq.

      apply validity_ty_ty in t'_Wt as SigmaA0B0_Wt.
      apply type_inv in SigmaA0B0_Wt as temp. dependent destruction temp.
      ty_inj_tac. subst.

      exists A0. exists (pi1 (ty n) (ty m) A0 B0 t').
      repeat split. econstructor; eauto.

    (* case pi2 *)
    - (* applying the ih to t *)
      edestruct H as (A' & t' & t'_Wt & erasure_t'_eq & erasure_A'_eq); eauto.
      subst.
      eapply validity_ty_ty in t'_Wt as A'_Wt. 
      eapply reduce_to in r as (A0 & B0 & n' & m' & eq1 & eq2 & A_eq & B_eq & T'_eq & l_eq); eauto.
      ty_inj_tac. subst.
      eapply type_conv in t'_Wt; eauto. clear T'_eq.

      apply validity_ty_ty in t'_Wt as SigmaA0B0_Wt.
      apply type_inv in SigmaA0B0_Wt as temp. dependent destruction temp.
      ty_inj_tac. subst.

      eexists. exists (pi2 (ty n) (ty m) A0 B0 t').
      repeat split. econstructor; eauto.
      erewrite erasure_subst_1_commutes; eauto.
      reflexivity.

    (* case pair' *)
    - edestruct H as (A' & t' & t'_Wt & erasure_t'_eq & erasure_A'_eq); eauto.
      subst.

      edestruct (H0 (Γ' ,, (ty n, A'))) as (_sort & B' & B'_Wt & erased_B'_eq & erased_sort_eq);
      eauto using ctx_typing, validity_ty_ty. subst.
      eapply reduce_to_sort in B'_Wt as (B'_Wt & l'_eq); eauto. subst.

      eassert (Γ' ⊢< _ > B' <[t'..] : Sort (ty m)) as B't'_Wt by eauto using subst_ty, subst_one.

      eapply H1 in B't'_Wt as (v' & v'Wt & erasure_v'); eauto using erasure_subst_1_commutes.
      subst.

      eexists. exists (pair (ty n) (ty m) A' B' t' v').
      repeat split.
      * econstructor; eauto using validity_ty_ty.
      * reflexivity.


    (* case Nat *)
    - eexists (Sort (ty 0)). eexists Nat. split; eauto using type_nat.

    (* case zero *)
    - eexists Nat. eexists zero. split; eauto using type_zero.

    (* case succ *)
    - (* applying the ih to t *)
      edestruct (H Γ' Nat) as (t' & t'_Wt & erasure_t'_eq); eauto using type_nat.
      subst.
      exists Nat. exists (succ t').
      repeat split; eauto using type_succ.

    (* case rec *)
    - (* applying the ih to P *)
      edestruct (H (Γ' ,, (ty 0, Nat))) as (_sort & P' & P'_Wt & erased_P'_eq & erased_sort_eq);
      eauto using ctx_cons, type_nat. subst.
      eapply reduce_to_sort in P'_Wt as (P'_Wt & l'_eq); eauto. subst.

      (* applying the ih to p_zero *)
      edestruct (H0 Γ' (P' <[ zero..])) as (p_zero' & p_zero'_Wt & erasure_eq); eauto.
      eapply (erasure_subst_1_commutes _ (ty 0)); eauto.
      eapply subst_ty; eauto using subst_one, type_zero.
      subst.

      (* applying the ih to p_succ *)
      edestruct (H1 (Γ' ,, (ty 0, Nat) ,, (l, P')) (P' <[ succ (var 1) .: ↑ >> (↑ >> var)]))
        as (p_succ' & p_succ'_Wt & erasure_eq); eauto.
      eapply aux_subst_commute; eauto.
      eapply subst_ty; eauto using subst_id_var1, ctx_typing, type_nat.
      subst.

      (* applying the ih to k *)
      edestruct (H2 Γ' Nat) as (k' & k'_Wt & erasure_eq); eauto using type_nat.
      subst.

      exists (P' <[ k' ..]). exists (rec l P' p_zero' p_succ' k').
      repeat split.
      auto using type_rec.
      eapply erasure_subst_1_commutes; eauto.
    
    (* case Eq *)
    - edestruct H as (_sort & A' & _A'_Wt & erased_A'_eq & erased_sort_eq); eauto. subst.
      eapply reduce_to_sort in r as (A'_Wt & _); eauto. clear _A'_Wt.

      edestruct H0 as (a' & a'_Wt & erasure_a'_eq); eauto. subst.
      edestruct H1 as (b' & b'_Wt & erasure_b'_eq); eauto. subst.
      eexists. exists (Eq i A' a' b').
      repeat split; eauto using type_Eq.

    (* case J*)
    - edestruct H as (_sort & A' & _A'_Wt & erased_A'_eq & erased_sort_eq); eauto. subst.
      eapply reduce_to_sort in r as (A'_Wt & _); eauto. clear _A'_Wt _sort i0 H.

      edestruct H0 as (a' & a'_Wt & erasure_a'_eq); eauto. subst.

      edestruct (H1 (Γ' ,, (l, A'))) as (_sort & P' & Wt_P' & erasure_P'_eq & erasure_sort_eq); eauto using ctx_typing.
      subst. eapply reduce_to_sort in Wt_P' as (Wt_P' & _); eauto.

      edestruct H2 as (p' & p'_Wt & erasure_p'_eq); eauto. 
      eapply (erasure_subst_1_commutes _ _); eauto.
      eapply subst_ty; eauto. eapply subst_one; eauto.

      edestruct H3 as (b' & b'_Wt & erasure_b'_eq); eauto. subst.

      edestruct H4 as (e' & e'_Wt & erasure_e'_eq); eauto.
      2:eapply type_Eq. 3:eapply a'_Wt. 3:eapply b'_Wt.
      1,2:eauto.
      subst.

      eexists. exists (J l i A' a' P' p' b' e').
      split; eauto using type_J.
      split; eauto. rewrite J_box_erasure. rewrite erasure_prop. reflexivity.
      eapply erasure_subst_1_commutes; eauto.
    
    (* case Lift *)
    - edestruct H as (_sort & A' & _A'_Wt & erased_A'_eq & erased_sort_eq); eauto. subst.
      eapply reduce_to_sort in r as (A'_Wt & _); eauto. clear _A'_Wt.
      eexists. exists (Lift i A').
      repeat split; eauto using type_Lift.

    (* case lower *)
    - edestruct H as (A' & t' & t'_Wt & erasure_t'_eq & erasure_A'_eq); eauto.
      subst.
      eapply validity_ty_ty in t'_Wt as A'_Wt. 
      eapply reduce_to in r as (A0 & A_eq & T'_eq & l_eq); eauto. subst.

      eapply type_conv in t'_Wt; eauto.

      eapply validity_ty_ty in t'_Wt as temp.
      eapply type_inv in temp. dependent destruction temp.

      exists A0. exists (lower i A0 t').
      repeat split; eauto using type_lower.

    (* case lower *)
    - edestruct H as (T & t' & t'_Wt & erased_t'_eq & erased_T_eq); eauto.
      subst.

      exists (Lift i T). exists (lift i T t').
      split; eauto using type_lift, validity_ty_ty.

    (* case cast *)
    - edestruct H as (U & e' & e'_Wt & erasure_e'_eq & erasure_U_eq); eauto.
      subst.
      eapply validity_ty_ty in e'_Wt as U_Wt. 
      eapply reduce_to in r as (V & A' & B' & sort_eq & A_eq & B_eq & U_conv_eq & _); eauto. subst. destruct V; dependent destruction sort_eq.
      
      eapply validity_conv_right in U_conv_eq as temp.
      eapply type_inv in temp. dependent destruction temp.
      clear A_Wt lvl_eq conv_ty. rename a_Wt into A'_Wt. rename b_Wt into B'_Wt.

      edestruct H0 as (a' & a'_Wt & erased_a'_eq); eauto. subst.
      exists B'. exists (cast i A' B' e' a'). 
      intuition eauto using typing.

    (* case injpi1 *)
    - edestruct H as (U & e' & e'_Wt & erasure_e'_eq & erasure_U_eq); eauto.
      subst.
      eapply validity_ty_ty in e'_Wt as U_Wt. 
      eapply reduce_to in r as (V & A' & B' & sort_eq & A_eq & B_eq & U_conv_eq & _); eauto.
      destruct V; dependent elimination sort_eq.
      destruct A'; dependent destruction A_eq. destruct B'; dependent destruction B_eq.

      eapply validity_conv_right in U_conv_eq as temp.
      eapply type_inv in temp. dependent destruction temp. clear lvl_eq conv_ty.
      eapply type_inv in a_Wt. dependent destruction a_Wt. clear lvl_eq conv_ty.
      eapply type_inv in b_Wt. dependent destruction b_Wt. clear lvl_eq conv_ty.

      eapply type_conv in e'_Wt; eauto.

      exists (Eq (Ax i) (Sort i) B'1 A'1).
      exists (injpi1 i (ty n) A'1 B'1 A'2 B'2 e').
      intuition eauto using typing.


    (* case injpi2 *)
    - edestruct H as (U & e' & e'_Wt & erasure_e'_eq & erasure_U_eq); eauto. clear H.
      subst.
      eapply validity_ty_ty in e'_Wt as U_Wt. 
      eapply reduce_to in r as (V & A' & B' & sort_eq & A_eq & B_eq & U_conv_eq & _); eauto.
      destruct V; dependent elimination sort_eq.
      destruct A'; dependent destruction A_eq. destruct B'; dependent destruction B_eq.

      eapply validity_conv_right in U_conv_eq as temp.
      eapply type_inv in temp. dependent destruction temp. clear lvl_eq conv_ty.
      eapply type_inv in a_Wt. dependent destruction a_Wt. clear lvl_eq conv_ty.
      eapply type_inv in b_Wt. dependent destruction b_Wt. clear lvl_eq conv_ty.

      eapply type_conv in e'_Wt; eauto.

      edestruct H0 as (a2' & a2'_Wt & erased_a2'_eq); eauto. subst. clear H0.

      eexists.
      exists (injpi2 i (ty n) A'1 B'1 A'2 B'2 e' a2').
      intuition eauto using typing. 
      simpl. f_equal.
      + unfold a1. etransitivity. 
        1:eapply erasure_subst_1_commutes; eauto.
        rasimpl. destruct i; simpl; reflexivity.
      + eapply erasure_subst_1_commutes; eauto.

    (* case annotation *)
    - (* applying the ih to T *)
      edestruct H as (_sort & T' & T'_Wt & erasure_T'_eq & erasure_sort_eq); eauto. subst.
      eapply reduce_to_sort in T'_Wt as (T'_Wt & l_eq); eauto. subst.

      (* applying the ih to t *)
      edestruct H0 as (t' & t'_Wt & erasure_t'_eq); eauto.

    (* case conv *)
    - subst.
      (* applying the ih to t *)
      edestruct H as (V' & t' & t'_Wt & erasure_t'_eq & erasure_V'_eq); eauto using validity_ty_ctx. subst.
      eapply validity_ty_ty in t'_Wt as V'_Wt.
      (* dependent destruction e. *)
      assert (Γ' ⊢< _ > T'0 ≡ V' : Sort _) by (eapply convcheck_sound; eauto).
      exists t'. split; eauto using type_conv, conv_sym.

    (* case lam *)
    - subst. (* we first derive that T' is convertible to Pi A' B',
         and that A' B' are well-typed *)
      eapply reduce_to in r as (A' & B' & A_eq & B_eq & T'_eq & l_eq); eauto. subst.
      apply validity_conv_right in T'_eq as Pi_Wt.
      apply type_inv in Pi_Wt as temp. dependent destruction temp.

      (* applying the ih to t *)
      edestruct H as (t' & t'_Wt & erased_t'_eq); eauto.
      unfold erase_ctx. reflexivity. subst.

      exists (lam i j A' B' t'). split; eauto using type_lam, type_conv, conv_sym, lam_box_erasure.

    (* case pair *)
    - subst.
      eapply reduce_to in r as (A' & B' & n' & m' & eq1 & eq2 & A_eq & B_eq & T'_eq & l_eq); eauto.
      ty_inj_tac. subst.
      apply validity_conv_right in T'_eq as temp.
      apply type_inv in temp. dependent destruction temp.
      ty_inj_tac. subst.

      edestruct H as (t' & t'Wt & erasure_t'); eauto.
      subst. 

      eassert (Γ' ⊢< _ > B' <[t'..] : Sort (ty m)) as B't'_Wt by eauto using subst_ty, subst_one, validity_ty_ctx.

      edestruct H0 as (u' & u'Wt & erasure_u'); eauto using erasure_subst_1_commutes.
      subst.

      exists (pair (ty n) (ty m) A' B' t' u').
      split.
      * eapply type_conv; eauto using conv_sym, typing.
      * reflexivity.
    
    (* case lift *)
    - subst. 
      eapply reduce_to in r as (A' & A_eq & T'_conv & l_eq); eauto. subst.
      apply validity_conv_right in T'_conv as temp.
      apply type_inv in temp as temp. dependent destruction temp.

      (* applying the ih to t *)
      edestruct H as (t' & t'_Wt & erased_t'_eq); eauto. subst.

      exists (lift i A' t').
      split; eauto using type_lift, type_conv, conv_sym.
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

Lemma gen_red Γ T l U :
    wt_is_wn ->
    Γ ⊢< Ax l > T ≡ U : Sort l ->
    match T with 
    | Sort i => 
        erasure (Ax (Ax i)) U -->> Sort i
    | Pi i j A B => 
        exists A' B',
        Γ ⊢< Ax i > A ≡ A' : Sort i /\
        Γ ,, (i, A) ⊢< Ax j > B ≡ B' : Sort j /\
        erasure (Ax (Ru i j)) U -->> Pi i j (erasure (Ax i) A') (erasure (Ax j) B')
    | Sigma i j A B =>
        exists A' B' n m,
        i = ty n /\ j = ty m /\
        Γ ⊢< Ax (ty n) > A ≡ A' : Sort (ty n) /\
        Γ ,, (ty n, A) ⊢< Ax (ty m) > B ≡ B' : Sort (ty m) /\
        erasure (Ax (Ru (ty n) (ty m))) U -->> Sigma (ty n) (ty m) (erasure (Ax i) A') (erasure (Ax (ty m)) B')
    | Lift i A => 
        exists A',
        Γ ⊢< Ax i > A ≡ A' : Sort i /\
        erasure (Ax (Ax i)) U -->> Lift i (erasure (Ax i) A')
    | Eq i A a b => 
        exists A' a' b',
        Γ ⊢< Ax i > A ≡ A' : Sort i /\
        Γ ⊢< i > a ≡ a' : A /\
        Γ ⊢< i > b ≡ b' : A /\
        erasure (Ax prop) U -->> Eq i (erasure (Ax i) A') (erasure i a') (erasure i b')
    | _ => True 
    end.
Proof.
    intros wt_is_wn T_conv_U.
    apply validity_conv_right in T_conv_U as U_Wt.
    pose proof U_Wt as U_Wt'.
    apply wt_is_wn in U_Wt as (Ve & erasure_U_red & Ve_nf).
    eapply subject_reduction_redd in U_Wt' as (V & U_eq_V & erasure_V); eauto.
    subst.
    assert (Γ ⊢< _ > T ≡ V : _) as T_eq_V by eauto using conv_trans.
    apply CR in T_eq_V as (W & tf_red_W & V_red_W).
    
    destruct T; eauto.

    all:eapply type_former_redd in tf_red_W; eauto; 
        rename tf_red_W into H' ; repeat destruct H' as (? & H'); subst.
    
    all:eapply validity_conv_left in T_conv_U as temp; 
    eapply type_inv in temp; dependent destruction temp; 
    eapply Ax_inj in lvl_eq; subst.

    all:eapply ortho_redd_to_eq in V_red_W; eauto;
        rewrite V_red_W in erasure_U_red; clear V_red_W;
        repeat eexists; eauto using redd_to_conv.
Qed.

Inductive label : Type := | agda | rocq.

Inductive CTerm : label -> cterm -> Prop :=

(* in agda we have non-annotated abstractions and pairs, and type ascriptions *)
| clam_ M : CTerm agda M -> CTerm agda (clam M)
| cann_ M MA : CTerm agda M -> CTerm agda MA -> CTerm agda (cann M MA)
| cpair_ Mt Mu : CTerm agda Mt -> CTerm agda Mu -> CTerm agda (cpair Mt Mu)

(* in rocq we have annotated abstractions and pairs, and no ascriptions *)
| clam'_ MA M : CTerm rocq MA -> CTerm rocq M -> CTerm rocq (clam' MA M)
| cpair'_ Mt MB Mu : CTerm rocq Mt -> CTerm rocq MB -> CTerm rocq Mu -> CTerm rocq (cpair' Mt MB Mu)

(* all the rest is the same *)
| cvar_ h n : CTerm h (cvar n)
| cSort_ h i : CTerm h (cSort i)
| cPi_ h MA MB : CTerm h MA -> CTerm h MB -> CTerm h (cPi MA MB)
| capp_ h M N : CTerm h M -> CTerm h N -> CTerm h (capp M N)
| cSigma_ h MA MB : CTerm h MA -> CTerm h MB -> CTerm h (cSigma MA MB)
| cpi1_ h M : CTerm h M -> CTerm h (cpi1 M)
| cpi2_ h M : CTerm h M -> CTerm h (cpi2 M)
| cNat_ h : CTerm h cNat
| czero_ h : CTerm h czero
| csucc_ h M : CTerm h M -> CTerm h (csucc M)
| crec_ h MP Mp_zero Mp_succ Mk : CTerm h MP -> CTerm h Mp_zero ->
    CTerm h Mp_succ -> CTerm h Mk -> CTerm h (crec MP Mp_zero Mp_succ Mk)
| cEq_ h MA Ma Mb : CTerm h MA -> CTerm h Ma -> CTerm h Mb -> CTerm h (cEq MA Ma Mb)
| cJ_ h MA Ma MP Mp Mb Me : CTerm h MA -> CTerm h Ma -> CTerm h MP ->
    CTerm h Mp -> CTerm h Mb -> CTerm h Me -> CTerm h (cJ MA Ma MP Mp Me Mb)
| cLift_ h MA : CTerm h MA -> CTerm h (cLift MA)
| clift_ h Ma : CTerm h Ma -> CTerm h (clift Ma)
| clower_ h Ma : CTerm h Ma -> CTerm h (clower Ma)
| ccast_ h Me Ma : CTerm h Me -> CTerm h Ma -> CTerm h (ccast Me Ma)
| cinjpi1_ h Me : CTerm h Me -> CTerm h (cinjpi1 Me)
| cinjpi2_ h Me Ma : CTerm h Me -> CTerm h Ma -> CTerm h (cinjpi2 Me Ma).


Fixpoint remove_cast_ann t :=
  match t with 
  | var _ => t
  | Sort _ => t
  | Pi i j A B => Pi i j (remove_cast_ann A) (remove_cast_ann B)
  | lam i j A B t => lam i j (remove_cast_ann A) (remove_cast_ann B) (remove_cast_ann t)
  | app i j A B t u => 
    app i j (remove_cast_ann A) (remove_cast_ann B) 
    (remove_cast_ann t) (remove_cast_ann u)
  | Sigma i j A B => Sigma i j (remove_cast_ann A) (remove_cast_ann B)
  | pair i j A B a b => 
    pair i j (remove_cast_ann A) (remove_cast_ann B)
    (remove_cast_ann a) (remove_cast_ann b)
  | pi1 i j A B t => 
    pi1 i j (remove_cast_ann A) (remove_cast_ann B) (remove_cast_ann t) 
  | pi2 i j A B t => 
    pi2 i j (remove_cast_ann A) (remove_cast_ann B) (remove_cast_ann t) 
  | Nat => t
  | zero => t
  | succ t => succ (remove_cast_ann t)
  | rec l P p0 ps t => 
    rec l (remove_cast_ann P) (remove_cast_ann p0) 
    (remove_cast_ann ps) (remove_cast_ann t)
  | Eq i A a b => Eq i (remove_cast_ann A) (remove_cast_ann a) (remove_cast_ann b) 
  | J l i A a P p b e => 
    J l i (remove_cast_ann A) (remove_cast_ann a) (remove_cast_ann P) 
    (remove_cast_ann p) (remove_cast_ann b) (remove_cast_ann e) 
  | Lift i A => Lift i (remove_cast_ann A)
  | lift i A a => lift i (remove_cast_ann A) (remove_cast_ann a)
  | lower i A a => lower i (remove_cast_ann A) (remove_cast_ann a)
  | cast i A B e a => 
    cast i box box (remove_cast_ann e) (remove_cast_ann a)
  | injpi1 i j A1 A2 B1 B2 e => 
    injpi1 i j (remove_cast_ann A1) (remove_cast_ann A2) 
    (remove_cast_ann B1) (remove_cast_ann B2) (remove_cast_ann e)
  | injpi2 i j A1 A2 B1 B2 e a => 
    injpi2 i j (remove_cast_ann A1) (remove_cast_ann A2) 
    (remove_cast_ann B1) (remove_cast_ann B2) (remove_cast_ann e) (remove_cast_ann a)
  | box => t
  end.


(* auxiliary lemma that only requires us to show the inferring case, 
   for the checking case we use the same term *)
Lemma completeness_aux_infer Γ l t T Δ h :
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


(* auxiliary lemma that only requires us to show the checking case, 
   for the inferring case we derive it by putting a type ascription.
   because of this, we also need to show the checking case for the type *)
Lemma completeness_aux_check Γ l t T Δ :
    wt_is_wn ->
    Γ ⊢< l > t : T ->
    ⊢ Γ ≡ Δ ->
    (exists MT U,
        (erase_ctx Δ) ⊢< Ax l > MT ⇒ (erasure (Ax (Ax l)) U) ↣ erasure (Ax l) T
        /\ Γ ⊢< Ax (Ax l) > Sort l ≡ U : Sort (Ax l)
        /\ CTerm agda MT) ->
    (forall U,
        Γ ⊢< Ax l > T ≡ U : Sort l ->
        exists M, (erase_ctx Δ) ⊢< l > M ⇐ (erasure (Ax l) U) ↣ (erasure l t) /\ CTerm agda M)
    ->
    (forall U,
        Γ ⊢< Ax l > T ≡ U : Sort l ->
        exists M, (erase_ctx Δ) ⊢< l > M ⇐ (erasure (Ax l) U) ↣ (erasure l t) /\ CTerm agda M)
    /\
    (exists M U,
        (erase_ctx Δ) ⊢< l > M ⇒ (erasure (Ax l) U) ↣ (erasure l t)
        /\ Γ ⊢< Ax l > T ≡ U : Sort l
        /\ CTerm agda M).
Proof.
    intros. split; eauto.
    destruct H2 as (MT & U & MT_infers & sort_conv & CMT).
    edestruct H3 as (M & M_checks & cM); eauto using validity_ty_ty, conv_refl.
    eapply gen_red in sort_conv; eauto.
    eexists (cann M MT). eexists. repeat split; eauto using validity_ty_ty, conv_refl, CTerm.
    eapply infer_ann; eauto using CTerm, redd_refl.
Qed.


(* we separate the case in the proof for pi, because we reuse it in the
  case for lam, when constructing the type annotation needed for inference *)
Lemma completeness_pi Γ i j A B h :
    wt_is_wn ->
    Γ ⊢< Ax i > A : Sort i ->
    Γ,, (i, A) ⊢< Ax j > B : Sort j ->
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
    intros wt_is_wn A_Wt B_Wt HA HB Δ Γ_eq_Δ.
    edestruct HA as (MA & UA & MA_infer & sort_eq_UA & CA); eauto.
    eapply gen_red in sort_eq_UA; eauto.

    edestruct HB as (MB & UB & MB_infer & sort_eq_UB & CB); eauto using conv_ccons, conv_refl.
    eapply gen_red in sort_eq_UB; eauto.

    exists (cPi MA MB). exists (Sort (Ru i j)).
    repeat split; eauto using CTerm, conv_sort, validity_ty_ctx. 
    eapply infer_pi; eauto.
Qed.

Lemma completeness_Sigma Γ n m A B h :
    wt_is_wn ->
    Γ ⊢< Ax (ty n) > A : Sort (ty n) ->
    Γ,, (ty n, A) ⊢< Ax (ty m) > B : Sort (ty m) ->
    (∀ Δ : ctx, ⊢ Γ ≡ Δ ->
        ∃ (M : cterm) (U : term), 
            erase_ctx Δ ⊢< Ax (ty n) > M ⇒ erasure (Ax (Ax (ty n))) U ↣ erasure (Ax (ty n)) A /\
            Γ ⊢< Ax (Ax (ty n)) > Sort (ty n) ≡ U : Sort (Ax (ty n)) ∧ CTerm h M) ->
    
    (∀ Δ : ctx, ⊢ Γ,, (ty n, A) ≡ Δ ->
        ∃ (M : cterm) (U : term),
            erase_ctx Δ ⊢< Ax (ty m) > M ⇒ erasure (Ax (Ax (ty m))) U ↣ erasure (Ax (ty m)) B ∧ 
            Γ,, (ty n, A) ⊢< Ax (Ax (ty m)) > Sort (ty m) ≡ U : Sort (Ax (ty m)) ∧ CTerm h M) ->
    forall Δ, ⊢ Γ ≡ Δ -> 
    ∃ (M : cterm) (U : term),
        erase_ctx Δ ⊢< Ax (ty (max n m)) > M ⇒ erasure (Ax (Ax (ty (max n m)))) U ↣ erasure (Ax (ty (max n m))) (Sigma (ty n) (ty m) A B) ∧ 
        Γ ⊢< Ax (Ax (ty (max n m))) > Sort (ty (max n m)) ≡ U : Sort (Ax (ty (max n m))) ∧ 
        CTerm h M.
Proof.
    intros wt_is_wn A_Wt B_Wt HA HB Δ Γ_eq_Δ.
    edestruct HA as (MA & UA & MA_infer & sort_eq_UA & CA); eauto.
    eapply gen_red in sort_eq_UA; eauto.

    edestruct HB as (MB & UB & MB_infer & sort_eq_UB & CB); eauto using conv_ccons, conv_refl.
    eapply gen_red in sort_eq_UB; eauto.

    exists (cSigma MA MB). eexists.
    repeat split; eauto using CTerm, conv_sort, validity_ty_ctx. 
    eapply infer_sigma; eauto.
Qed.

Lemma completeness_Lift Γ i A h :
    wt_is_wn ->
    Γ ⊢< Ax i > A : Sort i ->
    (∀ Δ : ctx, ⊢ Γ ≡ Δ →
        ∃ (M : cterm) (U : term),
            erase_ctx Δ ⊢< Ax i > M ⇒ erasure (Ax (Ax i)) U ↣ erasure (Ax i) A ∧
            Γ ⊢< Ax (Ax i) > Sort i ≡ U : Sort (Ax i) ∧ CTerm h M) ->
    forall Δ, ⊢ Γ ≡ Δ ->
    ∃ (M : cterm) (U : term),
        erase_ctx Δ ⊢< Ax (Ax i) > M ⇒ erasure (Ax (Ax (Ax i))) U ↣ erasure (Ax (Ax i)) (Lift i A) ∧
        Γ ⊢< Ax (Ax (Ax i)) > Sort (Ax i) ≡ U : Sort (Ax (Ax i)) ∧
        CTerm h M.
Proof.
    intros wt_is_wn A_Wt HA Δ Γ_eq_Δ.
    edestruct HA as (MA & UA & MA_infer & sort_eq_UA & CA); eauto.
    eapply gen_red in sort_eq_UA; eauto.

    exists (cLift MA). exists (Sort (Ax i)).
    repeat split; eauto using CTerm, conv_sort, validity_ty_ctx. 
    eapply infer_Lift; eauto.
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
    

    (* case var *)
    - eapply completeness_aux_infer; eauto.
      eapply conv_in_ctx_ty in Wt'; eauto.
      eapply type_inv in Wt'. dependent destruction Wt'.
      exists (cvar x). eexists.
      repeat split; eauto using CTerm.
      + eapply infer_var. apply varty_erase. eassumption.
      + eapply conv_in_ctx_conv; eauto using ctx_conv_sym.

    (* case sort *)
    - eapply completeness_aux_infer; eauto.
      exists (cSort l). exists (Sort (Ax l)).
      split; eauto using CTerm, conv_refl, validity_ty_ty, infer_Sort.

    (* case pi *)
    - eapply completeness_aux_infer; eauto.
      eapply completeness_pi; eauto. apply IHWt1; eauto. apply IHWt2; eauto.

    (* case lam *)
    - destruct h.
        + eapply completeness_aux_check; eauto.
          * eapply completeness_pi; eauto. apply IHWt1; eauto. apply IHWt2; eauto.
          * intros.
            eapply gen_red in H0 as (A' & B' & A_eq_A' & B_eq_B' & U_red_pi); eauto.
            edestruct IHWt3 as ((Mt & Mt_check & Ct) & _); eauto using conv_ccons, conv_refl.
            exists (clam Mt). erewrite lam_box_erasure; eauto. split; eauto using CTerm.
            eapply check_lam. apply U_red_pi. eauto.
        
        +   apply completeness_aux_infer; eauto.
            edestruct IHWt1 as (_ & MA & UA & MA_infer & sort_eq_UA & CA); eauto.
            eapply gen_red in sort_eq_UA; eauto.

            edestruct IHWt3 as (_ & Mt & B' & Mt_infer & B_eq_B' & CM); eauto using conv_ccons, conv_refl.

            exists (clam' MA Mt). exists (Pi i j A B').
            repeat split; eauto using CTerm.
            ++ erewrite lam_box_erasure; eauto. eapply infer_lam; eauto.
            ++ eauto using conv_pi, conv_refl.

    (* case app *)
    - eapply completeness_aux_infer; eauto. 
      edestruct IHWt3 as (_ & Mt & UA & Mr_infer & pi_eq_UA & Ct); eauto.
      eapply gen_red in pi_eq_UA as (A' & B' & A_eq_A' & B_eq_B' & erasure_UA_red); eauto.

      edestruct IHWt4 as ((Mu & Mu_check & Cu) & _); eauto.

      exists (capp Mt Mu). eexists (B' <[ u ..]). repeat split; eauto using CTerm.
      + erewrite app_box_erasure; eauto.
        erewrite erasure_subst_1_commutes; eauto using validity_conv_right.
        eapply infer_app; eauto.
      + eauto using subst_conv, subst_one, validity_conv_ctx, refl_subst.


    (* case sigma *)
    - eapply completeness_aux_infer; eauto.
      eapply completeness_Sigma; eauto. apply IHWt1; eauto. apply IHWt2; eauto.

    (* case pair *)
    - destruct h.
        + eapply completeness_aux_check; eauto.
          * eapply completeness_Sigma; eauto. apply IHWt1; eauto. apply IHWt2; eauto.
          * intros. clear IHWt1. clear IHWt2. 
            eapply gen_red in H0 as (A' & B' & n' & m' & eq1 & eq2 & A_eq_A' & B_eq_B' & U_red_pi); eauto.
            ty_inj_tac. subst.
            edestruct IHWt3 as ((Mt & Mt_check & Ct) & _); eauto.
            edestruct IHWt4 as ((Mu & Mu_check & Cu) & _); eauto.
            1:eapply subst_conv; eauto using validity_ty_ctx, substs_one, conv_refl.
            erewrite erasure_subst_1_commutes in Mu_check; eauto using validity_conv_right.
            exists (cpair Mt Mu). split; eauto using CTerm.
            simpl. eapply check_pair; eauto.
        
        +   apply completeness_aux_infer; eauto. clear IHWt1.
            edestruct IHWt3 as (_ & Ma & A' & Ma_infer & A_conv_A' & Ca); eauto.

            edestruct IHWt2 as (_ & MB & UB & MB_infer & sort_eq_UB & CB); eauto using  conv_ccons.
            eapply gen_red in sort_eq_UB; eauto.
    
            edestruct IHWt4 as ((Mb & Mb_check & Cb) & _); eauto using conv_refl, validity_ty_ty.
            erewrite erasure_subst_1_commutes in Mb_check; eauto.

            exists (cpair' Ma MB Mb). exists (Sigma (ty n) (ty m) A' B).
            repeat split; eauto using CTerm.
            ++ simpl. eapply infer_pair; eauto.
            ++ eauto using conv_sigma, conv_refl.

    (* case pi1 *)
    - eapply completeness_aux_infer; eauto. clear IHWt1 IHWt2.
      edestruct IHWt3 as (_ & Mt & UA & Mr_infer & sig_eq_UA & Ct); eauto.
      eapply gen_red in sig_eq_UA as (A' & B' & n' & m' & eq1 & eq2 & A_eq_A' & B_eq_B' & erasure_UA_red); eauto.
      ty_inj_tac. subst.

      exists (cpi1 Mt). eexists. repeat split; eauto using CTerm.
      simpl. econstructor; eauto.

    (* case pi2 *)
    - eapply completeness_aux_infer; eauto. clear IHWt1 IHWt2.
      edestruct IHWt3 as (_ & Mt & UA & Mr_infer & sig_eq_UA & Ct); eauto.
      eapply gen_red in sig_eq_UA as (A' & B' & n' & m' & eq1 & eq2 & A_eq_A' & B_eq_B' & erasure_UA_red); eauto.
      ty_inj_tac. subst.

      exists (cpi2 Mt). eexists. repeat split; eauto using CTerm; simpl.
      2:{eapply subst_conv; eauto using validity_ty_ctx, substs_one, conv_refl.
         eapply substs_one, conv_refl; econstructor; eauto. }
      erewrite erasure_subst_1_commutes; eauto using validity_conv_right. eapply infer_pi2; eauto.

    (* case nat *)
    - eapply completeness_aux_infer; eauto. 
      exists cNat. exists (Sort (ty 0)).
      split; eauto using conv_refl, validity_ty_ty, infer_Nat, CTerm.

    (* case zero *)
    - eapply completeness_aux_infer; eauto. 
      exists czero. exists Nat.
      split; eauto using conv_refl, validity_ty_ty, infer_zero, CTerm.

    (* case succ *)
    - eapply completeness_aux_infer; eauto. 
      edestruct IHWt as ((Mt & Mt_check & Ct) & _); eauto using validity_ty_ty, conv_refl.
      exists (csucc Mt). exists Nat.
      split; eauto using conv_refl, validity_ty_ty, infer_succ, CTerm.

    (* case rec *)
    - eapply completeness_aux_infer; eauto. 
      edestruct IHWt1 as (_ & MP & U & MP_infer & sort_eq_U & CP); eauto using conv_ccons, conv_nat, validity_ty_ctx.
      eapply gen_red in sort_eq_U; eauto.

      edestruct IHWt2 as ((Mp_zero & Mp_zero_check & Cp_zero) & _); eauto using conv_refl, validity_ty_ty.

      edestruct IHWt3 as ((Mp_succ & Mp_succ_check & Cp_succ) & _); eauto 7 using conv_ccons, conv_nat, conv_refl, validity_ty_ty.

      edestruct IHWt4 as ((Mt & Mt_check & Ct) & _); eauto using conv_refl, validity_ty_ty.

      exists (crec MP Mp_zero Mp_succ Mt). exists (P <[ t ..]).
      split; eauto using conv_refl, validity_ty_ty, CTerm.
      erewrite erasure_subst_1_commutes; eauto.
      eapply infer_rec; eauto; fold erasure.
      + erewrite erasure_subst_1_commutes in Mp_zero_check; eauto. eauto.
      + erewrite aux_subst_commute in Mp_succ_check; eauto.
    

    (* case Eq *)
    - eapply completeness_aux_infer; eauto. 
      edestruct IHWt1 as (_ & MA & UA & MA_infer & sort_eq_UA & CA); eauto.
      eapply gen_red in sort_eq_UA; eauto.

      edestruct IHWt2 as ((Ma & Ma_checks & Ca) & _); eauto using conv_refl.
      edestruct IHWt3 as ((Mb & Mb_checks & Cb) & _); eauto using conv_refl.

      eexists (cEq MA Ma Mb). eexists (Sort prop). repeat split; eauto using CTerm, conv_sort, validity_ty_ctx.
      simpl. eapply infer_eq; eauto.

    (* case J *)
    - eapply completeness_aux_infer; eauto. 
      edestruct IHWt1 as (_ & MA & UA & MA_infer & sort_eq_UA & CA); eauto.
      eapply gen_red in sort_eq_UA; eauto. clear IHWt1.
    
      edestruct IHWt2 as ((Ma & Ma_checks & Ca) & _); eauto using conv_refl. clear IHWt2.
      edestruct IHWt5 as ((Mb & Mb_checks & Cb) & _); eauto using conv_refl. clear IHWt5.

      edestruct IHWt3 as (_ & MP & UP & MP_infer & sort_eq_UP & CP); eauto using ConvCtx, conv_refl.
      eapply gen_red in sort_eq_UP; eauto. clear IHWt3.

      edestruct IHWt4 as ((Mp & Mp_checks & Cp) & _); eauto using conv_refl, subst_ty, conv_refl, subst_one, validity_ty_ctx. 
      clear IHWt4.

      edestruct IHWt6 as ((Me & Me_checks & Ce) & _); eauto using conv_refl, validity_ty_ty, conv_refl.
      clear IHWt6.

      exists (cJ MA Ma MP Mp Mb Me). eexists.
      repeat split;eauto using conv_refl, subst_ty, conv_refl, subst_one, validity_ty_ctx, CTerm. 
      erewrite erasure_subst_1_commutes; eauto.
      simpl. eapply infer_J; eauto.
      + erewrite erasure_subst_1_commutes in Mp_checks; eauto. 
      + rewrite erasure_prop in Me_checks. eauto.


    (* case Lift *)
    - eapply completeness_aux_infer; eauto. 
      eapply completeness_Lift; eauto.  intros. eapply IHWt; eauto.


    (* case lift *)
    - destruct h.
      + eapply completeness_aux_check; eauto.
        * eapply completeness_Lift; eauto. eapply IHWt1; eauto.

        * intros. 
          eapply gen_red in H0 as (A' & A_eq_A' & erasure_UA_red); eauto.
          edestruct IHWt2 as (H' & _); eauto.
          eapply H' in A_eq_A' as (M & M_checks & CM).
          exists (clift M). split; eauto using CTerm.
          eapply check_lift; eauto.
          
      + eapply completeness_aux_infer; eauto. 
        edestruct IHWt2 as (_ & Mt & UA & Mr_infer & Lift_eq_UA & Ct); eauto.
        exists (clift Mt). eexists. repeat split; eauto using CTerm.
        2:eauto using conv_Lift.
        simpl. eapply infer_lift; eauto.

    (* case lower *)
    - eapply completeness_aux_infer; eauto. 
      edestruct IHWt2 as (_ & Mt & UA & Mr_infer & Lift_eq_UA & Ct); eauto.
      eapply gen_red in Lift_eq_UA as (A' & A_eq_A' & erasure_UA_red); eauto.

      exists (clower Mt). eexists. repeat split; eauto using CTerm.
      eapply infer_lower; eauto.

    
    - eapply completeness_aux_infer; eauto.  clear IHWt1 IHWt2.
      edestruct IHWt3 as (_ & Me & UA & Me_infer & Eq_eq_UA & Ce); eauto. clear IHWt3.
      eapply gen_red in Eq_eq_UA as (_sort & A' & B' & sort_conv_sort & A_conv_A' & B_conv_B' & erasure_UA_red); eauto.
      eapply gen_red in sort_conv_sort; eauto.
      
      assert (erasure (Ax prop) UA -->> Eq (Ax i) (Sort i) (erasure (Ax i) A')
(erasure (Ax i) B')) by admit.

      edestruct IHWt4 as ((Ma & Ma_check & Ca) & _); eauto. clear IHWt4.
      exists (ccast Me Ma). exists B.
      repeat split; eauto using CTerm.
      eapply infer_cast; eauto; fold erasure.

      


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
    eauto using ctx_conv_refl, validity_ty_ctx.
    eapply case_check. eauto using validity_ty_ty, conv_refl.
Qed.

Corollary completeness_infer Γ l t T h :
    wt_is_wn -> Γ ⊢< l > t : T ->
    exists M U, (erase_ctx Γ) ⊢< l > M ⇒ (erasure (Ax l) U) ↣ (erasure l t)
        /\ Γ ⊢< Ax l > T ≡ U : Sort l  /\ CTerm h M.
Proof.
    intros. pose proof H0 as Wt.
    eapply completeness in Wt as (case_check & case_infer);
    eauto using ctx_conv_refl, validity_ty_ctx.
Qed.


Print Assumptions completeness_infer.
