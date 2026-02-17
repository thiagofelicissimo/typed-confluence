
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
| cJ : cterm -> cterm -> cterm -> cterm

| cLift : cterm -> cterm
| clift : cterm -> cterm
| clower : cterm -> cterm

| ccast : cterm -> cterm -> cterm
| cinjpi1 : cterm -> cterm
| cinjpi2 : cterm -> cterm -> cterm

| csum : cterm → cterm → cterm
| cinl : cterm → cterm
| iinl (B a : cterm)
| cinr : cterm → cterm
| iinr (A b : cterm)
| csum_case : cterm → cterm → cterm → cterm → cterm.

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

Definition inl_box a := inl prop prop box box a.

Definition inr_box a := inr prop prop box box a.

Definition sum_case_box l P pl pr u :=
  match l with
  | prop => box
  | _ => sum_case prop prop l box box P pl pr u
  end.

Inductive infer : ctx -> level -> cterm → term -> term → Prop :=
| infer_var Γ x l A :
    Γ ∋< l > x : A →
    Γ ⊢< l > cvar x ⇒ A ↣ box_if_prop l (var x)

| infer_Sort Γ l :
    Γ ⊢< Ax (Ax l) > cSort l ⇒ Sort (Ax l) ↣ Sort l

| infer_pi Γ i j i' j' T U MA MB A B :
    Γ ⊢< i' > MA ⇒ T ↣ A ->
    T -->> Sort i ->
    Γ ,, (i , A) ⊢< j' > MB ⇒ U ↣ B ->
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

| infer_eq Γ i' i MA T A Ma a Mb b : 
    Γ ⊢< i' > MA ⇒ T ↣ A ->
    T -->> Sort i ->
    Γ ⊢< i > Ma ⇐ A ↣ a ->
    Γ ⊢< i > Mb ⇐ A ↣ b ->
    Γ ⊢< Ax prop > cEq MA Ma Mb ⇒ Sort prop ↣ Eq i A a b

| infer_J Γ l T A a i i' MP U P Mp p b Me e :
    Γ ⊢< prop > Me ⇒ T ↣ e -> 
    T -->> Eq l A a b ->
    Γ ,, (l, A) ⊢< i' > MP ⇒ U ↣ P ->
    U -->> Sort i ->
    Γ ⊢< i > Mp ⇐ P<[a..] ↣ p ->
    Γ ⊢< i > cJ MP Mp Me ⇒ P <[b..] ↣ J_box l i A a P p b e

| infer_Lift Γ i' i MA T A :
    Γ ⊢< i' > MA ⇒ T ↣ A ->
    T -->> Sort i ->
    Γ ⊢< Ax (Ax i) > cLift MA ⇒ Sort (Ax i) ↣ Lift i A

| infer_lower Γ i' i Ma T a A :
    Γ ⊢< i' > Ma ⇒ T ↣ a ->
    T -->> Lift i A ->
    Γ ⊢< i > clower Ma ⇒ A ↣ lower_box i a

| infer_lift Γ i Ma a A :
    Γ ⊢< i > Ma ⇒ A ↣ a ->
    Γ ⊢< Ax i > clift Ma ⇒ Lift i A ↣ lift prop box a

| infer_cast Γ Me T e i' i A B Ma a :
    Γ ⊢< i' > Me ⇒ T ↣ e ->
    T -->> Eq (Ax i) (Sort i) A B ->
    Γ ⊢< i > Ma ⇐ A ↣ a ->
    Γ ⊢< i > ccast Me Ma ⇒ B ↣ cast_box i A B a

| infer_injpi1 Γ Me T e i' i n A1 B1 A2 B2 :
    Γ ⊢< i' > Me ⇒ T ↣ e ->
    T -->> Eq (Ax (Ru i (ty n))) (Sort (Ru i (ty n))) 
            (Pi i (ty n) A1 B1) (Pi i (ty n) A2 B2) ->
    Γ ⊢< prop > cinjpi1 Me ⇒ Eq (Ax i) (Sort i) A2 A1 ↣ box

| infer_injpi2 Γ Me T e i i' n A1 B1 A2 B2 Ma a2 :
    Γ ⊢< i' > Me ⇒ T ↣ e ->
    T -->> Eq (Ax (Ru i (ty n))) (Sort (Ru i (ty n))) 
            (Pi i (ty n) A1 B1) (Pi i (ty n) A2 B2) ->
    Γ ⊢< i > Ma ⇐ A2 ↣ a2 ->
    let a1 := cast_box i A2 A1 a2 in
    Γ ⊢< prop > cinjpi2 Me Ma ⇒ Eq (Ax (ty n)) (Sort (ty n)) (B1<[a1..]) (B2 <[a2..]) ↣ box

| infer_sum Γ i' j' n m MA TA A MB TB B :
    Γ ⊢< i' > MA ⇒ TA ↣ A →
    TA -->> Sort (ty n) →
    Γ ⊢< Ax j' > MB ⇒ TB ↣ B →
    TB -->> Sort (ty m) →
    Γ ⊢< Ax (ty (max n m)) > csum MA MB ⇒ Sort (ty (max n m)) ↣ tysum (ty n) (ty m) A B

| infer_inl Γ j n m A MB TB B Ma a :
    Γ ⊢< ty n > Ma ⇒ A ↣ a →
    Γ ⊢< j > MB ⇒ TB ↣ B →
    TB -->> Sort (ty m) →
    Γ ⊢< ty (max n m) > iinl MB Ma ⇒ tysum (ty n) (ty m) A B ↣ inl_box a

| infer_inr Γ i n m MA TA A B Mb b :
    Γ ⊢< ty m > Mb ⇒ B ↣ b →
    Γ ⊢< i > MA ⇒ TA ↣ A →
    TA -->> Sort (ty n) →
    Γ ⊢< ty (max n m) > iinr MA Mb ⇒ tysum (ty n) (ty m) A B ↣ inr_box b

| infer_sum_case Γ Mu Tu u k i j A B MP TP P sl l Mpl pl Mpr pr :
    Γ ⊢< k > Mu ⇒ Tu ↣ u →
    Tu -->> tysum (ty i) (ty j) A B →
    Γ ,, (ty (max i j), tysum (ty i) (ty j) A B) ⊢< sl > MP ⇒ TP ↣ P →
    TP -->> Sort l →
    Γ ,, (ty i, A) ⊢< l > Mpl ⇐ P <[ (inl_box (var 0)) .: S >> var ] ↣ pl →
    Γ ,, (ty j, B) ⊢< l > Mpr ⇐ P <[ (inr_box (var 0)) .: S >> var ] ↣ pr →
    Γ ⊢< l > csum_case MP Mpl Mpr Mu ⇒ P <[ u .. ] ↣ sum_case_box l P pl pr u

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

| check_pair Γ i n m Mt A t T B Mu u :
    T -->> Sigma (ty n) (ty m) A B ->
    Γ ⊢< ty n > Mt ⇐ A ↣ t ->
    Γ ⊢< ty m > Mu ⇐ B <[t..] ↣ u ->
    Γ ⊢< i > cpair Mt Mu ⇐ T ↣ pair_box t u    

| check_lift Γ l i Ma a T A :
    T -->> Lift i A ->
    Γ ⊢< i > Ma ⇐ A ↣ a ->
    Γ ⊢< l > clift Ma ⇐ T ↣ lift prop box a

| check_inl Γ Ma a T i j A B l :
    T -->> tysum (ty i) (ty j) A B →
    Γ ⊢< ty i > Ma ⇐ A ↣ a →
    Γ ⊢< l > cinl Ma ⇐ T ↣ inl_box a

| check_inr Γ Mb b T i j A B l :
    T -->> tysum (ty i) (ty j) A B →
    Γ ⊢< ty j > Mb ⇐ B ↣ b →
    Γ ⊢< l > cinr Mb ⇐ T ↣ inr_box b

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
  Γ ⊢< Ax j > t : Sort j ∧ l = Ax j.
Proof.
  intros t_Wt erasure_red.
  eapply subject_reduction_redd in erasure_red as (_sort & TA_eq_sort & erasure_sort_eq_sort) ; eauto using validity_ty_ty.
  destruct _sort; dependent destruction erasure_sort_eq_sort.
  apply validity_conv_right in TA_eq_sort as Sort_wt.
  apply type_inv in Sort_wt. dependent destruction Sort_wt.
  apply Ax_inj in lvl_eq. subst.
  split; eauto using type_conv.
Qed.

Ltac Ax_inj_tac :=
  repeat match goal with
  | H : Ax _ = Ax _ |- _ => eapply Ax_inj in H
  end.

Lemma reduce_to Γ l T U :
  Γ ⊢< Ax l > T : Sort l ->
  erasure (Ax l) T -->> U ->
  match U with
  | Pi i j A B =>
      exists A' B',
      A = erasure (Ax i) A' ∧
      B = erasure (Ax j) B' ∧
      Γ ⊢< Ax (Ru i j) > T ≡ Pi i j A' B' : Sort (Ru i j) ∧
      l = Ru i j
  | Sigma i j A B =>
      exists A' B' n m,
      i = ty n ∧
      j = ty m ∧
      A = erasure (Ax (ty n)) A' ∧
      B = erasure (Ax (ty m)) B' ∧
      Γ ⊢< Ax (ty (max n m)) > T ≡ Sigma (ty n) (ty m) A' B' : Sort (ty (max n m)) ∧
      l = ty (max n m)
  | Lift i A =>
      exists A',
      A = erasure (Ax i) A' ∧
      Γ ⊢< Ax (Ax i) > T ≡ Lift i A' : Sort (Ax i) ∧
      l = Ax i
  | Eq i A a b =>
      exists A' a' b',
      A = erasure (Ax i) A' ∧
      a = erasure i a' ∧
      b = erasure i b' ∧
      Γ ⊢< Ax prop > T ≡ Eq i A' a' b' : Sort prop ∧
      l = prop
  | tysum i j A B =>
      ∃ A' B' n m,
        i = ty n ∧
        j = ty m ∧
        A = erasure (Ax (ty n)) A' ∧
        B = erasure (Ax (ty m)) B' ∧
        Γ ⊢< Ax (ty (max n m)) > T ≡ tysum (ty n) (ty m) A' B' : Sort (ty (max n m)) ∧
        l = ty (max n m)
  | _ => True
  end.
Proof.
  intros t_Wt erasure_red.
  eapply subject_reduction_redd in erasure_red as (_ty & TA_eq_ty & erasure_ty_eq_ty) ; eauto using validity_ty_ty.
  destruct U; eauto.

  all:destruct _ty; dependent destruction erasure_ty_eq_ty;
  apply validity_conv_right in TA_eq_ty as ty_wt;
  apply type_inv in ty_wt as temp; dependent destruction temp;
  Ax_inj_tac ; subst; repeat eexists; eauto using type_conv.
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

Lemma sum_case_box_erasure i j l A B P pl pr u :
  erasure l (sum_case i j l A B P pl pr u) =
  sum_case_box l (erasure (Ax l) P) (erasure l pl) (erasure l pr) (erasure (Ru i j) u).
Proof.
  destruct l. all: reflexivity.
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

Lemma inl_subst_comm Γ l n m A B P :
  Γ ,, (ty (max n m), tysum (ty n) (ty m) A B) ⊢< Ax l > P : Sort l →
  erasure (Ax l) (P <[ inl (ty n) (ty m) (S ⋅ A) (S ⋅ B) (var 0) .: S >> var ]) =
  (erasure (Ax l) P) <[ inl_box (var 0) .: S >> var ].
Proof.
  intros h.
  erewrite erasure_subst_commutes with (f := λ _, ty 0). 2: eassumption.
  - apply ext_term. intros []. all: reflexivity.
  - apply refines_all.
Qed.

Lemma inr_subst_comm Γ l n m A B P :
  Γ ,, (ty (max n m), tysum (ty n) (ty m) A B) ⊢< Ax l > P : Sort l →
  erasure (Ax l) (P <[ inr (ty n) (ty m) (S ⋅ A) (S ⋅ B) (var 0) .: S >> var ]) =
  (erasure (Ax l) P) <[ inr_box (var 0) .: S >> var ].
Proof.
  intros h.
  erewrite erasure_subst_commutes with (f := λ _, ty 0). 2: eassumption.
  - apply ext_term. intros []. all: reflexivity.
  - apply refines_all.
Qed.

Theorem sound :
  (forall Γ l M T t, Γ ⊢< l > M ⇒ T ↣ t ->
      forall Γ'
      (erased_Γ'_eq : erase_ctx Γ' = Γ)
      (Γ'Wf : ⊢ Γ'),
      exists T' t', Γ' ⊢< l > t' : T' ∧ erasure l t' = t ∧ erasure (Ax l) T' = T
  ) ∧ (
  forall Γ l M T t, Γ ⊢< l > M ⇐ T ↣ t ->
      forall Γ' T'
      (erased_Γ'_eq : erase_ctx Γ' = Γ)
      (erased_T'_eq : erasure (Ax l) T' = T)
      (T'Wt : Γ' ⊢< Ax l > T' : Sort l),
      exists t', Γ' ⊢< l > t' : T' ∧ erasure l t' = t
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
      eapply reduce_to_sort in A'_Wt as (A'_Wt & eq); eauto. subst.

      (* applying the ih to B *)
      edestruct (H0 (Γ' ,, (i, A'))) as (TB & B' & B'_Wt & erased_B'_eq & erased_TB_eq).
      all: (eauto using ctx_cons, conv_sort). subst.
      eapply reduce_to_sort in B'_Wt as (B'_Wt & eq); eauto. subst.

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
      eapply reduce_to_sort in r as (A'_Wt & eq); eauto.
      subst. clear _A'_Wt.

  (* case Eq *)
  - edestruct H as (_sort & A' & _A'_Wt & erased_A'_eq & erased_sort_eq); eauto. subst.
    eapply reduce_to_sort in r as (A'_Wt & _); eauto. clear _A'_Wt.

    edestruct H0 as (a' & a'_Wt & erasure_a'_eq); eauto. subst.
    edestruct H1 as (b' & b'_Wt & erasure_b'_eq); eauto. subst.
    eexists. exists (Eq i A' a' b').
    repeat split; eauto using type_Eq.

  (* case J*)
  - edestruct H as (V & e' & e'_Wt & erased_t'_eq & erased_V_eq); eauto.
    subst. clear H.
    eapply reduce_to in r as (A' & a' & b' & A_eq & a_eq & b_eq & eqconv & _); eauto using validity_ty_ty.
    subst.

      edestruct (H0 (Γ' ,, (l, A'))) as (_sort & P' & Wt_P' & erasure_P'_eq & erasure_sort_eq); eauto using ctx_typing. 
      subst. clear H0.
      subst. eapply reduce_to_sort in Wt_P' as (Wt_P' & eq); eauto.
      subst.

    edestruct (H0 (Γ' ,, (l, A'))) as (_sort & P' & Wt_P' & erasure_P'_eq & erasure_sort_eq); eauto using ctx_typing.
    subst. clear H0.
    subst. eapply reduce_to_sort in Wt_P' as (Wt_P' & _); eauto.

      eexists. exists (J l i A' a' P' p' b' e').
      split; eauto using type_J, type_conv.
      split; eauto. rewrite J_box_erasure. rewrite erasure_prop. reflexivity.
      eapply erasure_subst_1_commutes; eauto.
    
    (* case Lift *)
    - edestruct H as (_sort & A' & _A'_Wt & erased_A'_eq & erased_sort_eq); eauto. subst.
      eapply reduce_to_sort in r as (A'_Wt & eq); eauto. clear _A'_Wt. subst.
      eexists. exists (Lift i A').
      repeat split; eauto using type_Lift.

    edestruct H1 as (p' & p'_Wt & erasure_p'_eq); eauto.
    eapply (erasure_subst_1_commutes _ _); eauto.
    eapply subst_ty; eauto. eapply subst_one; eauto.
    subst. clear H1.

    eexists. exists (J l i A' a' P' p' b' e').
    split; eauto using type_J, type_conv.
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

    (* case cast *)
    - edestruct H as (U & e' & e'_Wt & erasure_e'_eq & erasure_U_eq); eauto.
      subst.
      eapply validity_ty_ty in e'_Wt as U_Wt. 
      eapply reduce_to in r as (V & A' & B' & sort_eq & A_eq & B_eq & U_conv_eq & eq); eauto. subst. destruct V; dependent destruction sort_eq.
      
      eapply validity_conv_right in U_conv_eq as temp.
      eapply type_inv in temp. dependent destruction temp.
      clear A_Wt lvl_eq conv_ty. rename a_Wt into A'_Wt. rename b_Wt into B'_Wt.

  (* case lower *)
  - edestruct H as (T & t' & t'_Wt & erased_t'_eq & erased_T_eq); eauto.
    subst.

    (* case injpi1 *)
    - edestruct H as (U & e' & e'_Wt & erasure_e'_eq & erasure_U_eq); eauto.
      subst.
      eapply validity_ty_ty in e'_Wt as U_Wt. 
      eapply reduce_to in r as (V & A' & B' & sort_eq & A_eq & B_eq & U_conv_eq & eq); eauto. subst.
      destruct V; dependent elimination sort_eq.
      destruct A'; dependent destruction A_eq. destruct B'; dependent destruction B_eq.

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

    (* case injpi2 *)
    - edestruct H as (U & e' & e'_Wt & erasure_e'_eq & erasure_U_eq); eauto. clear H.
      subst.
      eapply validity_ty_ty in e'_Wt as U_Wt. 
      eapply reduce_to in r as (V & A' & B' & sort_eq & A_eq & B_eq & U_conv_eq & eq); eauto. subst.
      destruct V; dependent elimination sort_eq.
      destruct A'; dependent destruction A_eq. destruct B'; dependent destruction B_eq.

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

  (* tysum *)
  - (* applying the ih to A *)
    edestruct H as (TA' & A' & A'_Wt & erased_A'_eq & erased_TA_eq); eauto.
    subst.
    eapply reduce_to_sort in A'_Wt as (A'_Wt & lvleq); eauto. subst.

    (* applying the ih to B *)
    edestruct H0 as (TB' & B' & B'_Wt & erased_B'_eq & erased_TB_eq).
    all: eauto.
    subst.
    eapply reduce_to_sort in B'_Wt as (B'_Wt & lvl_eq); eauto.
    Ax_inj_tac. subst.

    exists (Sort (ty (max n m))), (tysum (ty n) (ty m) A' B').
    repeat split. econstructor; eauto.

  (* inl *)
  - edestruct H as (A' & a' & ha & ea & eA); eauto.
    subst.

    edestruct H0 as (TB' & B' & B'_Wt & erased_B'_eq & erased_TB_eq).
    all: eauto.
    subst.
    eapply reduce_to_sort in B'_Wt as (B'_Wt & lvl_eq); eauto.
    subst.

    eexists. exists (inl (ty n) (ty m) A' B' a').
    repeat split.
    * econstructor; eauto using validity_ty_ty.
    * reflexivity.

  (* inr *)
  - edestruct H as (B' & b' & hb & eb & eB); eauto.
    subst.

    edestruct H0 as (TA' & A' & A'_Wt & eA & eTA).
    all: eauto.
    subst.
    eapply reduce_to_sort in A'_Wt as (A'_Wt & lvl_eq); eauto.
    subst.

    eexists. exists (inr (ty n) (ty m) A' B' b').
    repeat split.
    * econstructor; eauto using validity_ty_ty.
    * reflexivity.

  (* sum_case *)
  - edestruct H as (Tu' & u' & hu' & eu & es); eauto.
    subst.
    eapply validity_ty_ty in hu' as hTu'.
    eapply reduce_to in r as (A' & B' & n & m & ? & ? & -> & -> & eT & ->); eauto.
    ty_inj_tac. subst.
    eapply type_conv in hu'; eauto. clear eT hTu'.
    eapply validity_ty_ty in hu' as hsum.
    eapply type_inv in hsum as hh. dependent destruction hh.

    edestruct (H0 (Γ' ,, (ty (max n m), tysum (ty n) (ty m) A' B'))) as (TP' & P' & hP & eP & eTP).
    all: (eauto using ctx_cons, conv_sort). subst.
    eapply reduce_to_sort in hP as (hP & e). 2: eauto.
    subst.

    edestruct (H1 (Γ' ,, (ty n, A'))) as (pl' & hpl & epl). all: eauto.
    1:{ eapply inl_subst_comm. eassumption. }
    1:{
      eapply subst_ty.
      all: eauto with sidecond.
      apply well_scons_alt. 1: eauto with sidecond.
      rasimpl. econstructor. all: eauto using type_ren with sidecond.
      econstructor. all: eauto with sidecond.
    }
    subst.

    edestruct (H2 (Γ' ,, (ty m, B'))) as (pr' & hpr & epr). all: eauto.
    1:{ eapply inr_subst_comm. eassumption. }
    1:{
      eapply subst_ty.
      all: eauto with sidecond.
      apply well_scons_alt. 1: eauto with sidecond.
      rasimpl. econstructor. all: eauto using type_ren with sidecond.
      econstructor. all: eauto with sidecond.
    }
    subst.

    eexists _, (sum_case (ty n) (ty m) l A' B' P' pl' pr' u').
    repeat split.
    + econstructor; eauto.
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

  (* inl *)
  - subst.
    eapply reduce_to in r as (A' & B' & n & m & ? & ? & -> & -> & hT & ->).
    2: eassumption.
    ty_inj_tac. subst.

    eapply validity_conv_right in hT as hsum.
    eapply type_inv in hsum as hh. dependent destruction hh.

    edestruct H as (a' & ha & <-); eauto.

    exists (inl (ty n) (ty m) A' B' a').
    repeat split.
    eauto using type_conv, conv_sym, typing.

  (* inr *)
  - subst.
    eapply reduce_to in r as (A' & B' & n & m & ? & ? & -> & -> & hT & ->).
    2: eassumption.
    ty_inj_tac. subst.

    eapply validity_conv_right in hT as hsum.
    eapply type_inv in hsum as hh. dependent destruction hh.

    edestruct H as (b' & hb & <-); eauto.

    exists (inr (ty n) (ty m) A' B' b').
    repeat split.
    eauto using type_conv, conv_sym, typing.
Qed.


Corollary infer_sound Γ l M t T :
  ⊢ Γ ->
  (erase_ctx Γ) ⊢< l > M ⇒ T ↣ t ->
  exists T' t', Γ ⊢< l > t' : T' ∧ erasure l t' = t ∧ erasure (Ax l) T' = T.
Proof.
  intros. eapply (proj1 sound); eauto.
Qed.


Corollary check_sound Γ l M t T :
  Γ ⊢< Ax l > T : Sort l ->
  (erase_ctx Γ) ⊢< l > M ⇐ (erasure (Ax l) T) ↣ t ->
  exists t', Γ ⊢< l > t' : T ∧ erasure l t' = t.
Proof.
  intros. eapply (proj2 sound); eauto.
Qed.

Definition wt_is_wn :=
  forall Γ l t A,
    Γ ⊢< l > t : A ->
    exists u, (erasure l t) -->> u ∧ nf u.

Lemma gen_red Γ T l U :
  wt_is_wn ->
  Γ ⊢< Ax l > T ≡ U : Sort l ->
  match T with
  | Sort i =>
      erasure (Ax (Ax i)) U -->> Sort i
  | Pi i j A B =>
      ∃ A' B',
        Γ ⊢< Ax i > A ≡ A' : Sort i ∧
        Γ ,, (i, A) ⊢< Ax j > B ≡ B' : Sort j ∧
        erasure (Ax (Ru i j)) U -->>
        Pi i j (erasure (Ax i) A') (erasure (Ax j) B')
  | Sigma i j A B =>
      ∃ A' B' n m,
        i = ty n ∧ j = ty m ∧
        Γ ⊢< Ax (ty n) > A ≡ A' : Sort (ty n) ∧
        Γ ,, (ty n, A) ⊢< Ax (ty m) > B ≡ B' : Sort (ty m) ∧
        erasure (Ax (Ru (ty n) (ty m))) U -->>
        Sigma (ty n) (ty m) (erasure (Ax i) A') (erasure (Ax (ty m)) B')
  | Lift i A =>
      ∃ A',
        Γ ⊢< Ax i > A ≡ A' : Sort i ∧
        erasure (Ax (Ax i)) U -->> Lift i (erasure (Ax i) A')
  | Eq i A a b =>
      ∃ A' a' b',
        Γ ⊢< Ax i > A ≡ A' : Sort i ∧
        Γ ⊢< i > a ≡ a' : A ∧
        Γ ⊢< i > b ≡ b' : A ∧
        erasure (Ax prop) U -->> Eq i (erasure (Ax i) A') (erasure i a') (erasure i b')
  | tysum i j A B =>
      ∃ A' B' n m,
        i = ty n ∧
        j = ty m ∧
        Γ ⊢< Ax (ty n) > A ≡ A' : Sort (ty n) ∧
        Γ ⊢< Ax (ty m) > B ≡ B' : Sort (ty m) ∧
        erasure (Ax (Ru (ty n) (ty m))) U -->>
        tysum (ty n) (ty m) (erasure (Ax i) A') (erasure (Ax (ty m)) B')
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
  Ax_inj_tac ; subst.

  all:eapply ortho_redd_to_eq in V_red_W; eauto;
      rewrite V_red_W in erasure_U_red; clear V_red_W;
      repeat eexists; eauto using redd_to_conv.
Qed.

Inductive label : Type := agda | rocq.

Inductive CTerm : label -> cterm -> Prop :=

(* in Agda we have non-annotated abstractions and pairs, and type ascriptions *)
| clam_ M : CTerm agda M -> CTerm agda (clam M)
| cann_ M MA : CTerm agda M -> CTerm agda MA -> CTerm agda (cann M MA)
| cpair_ Mt Mu : CTerm agda Mt -> CTerm agda Mu -> CTerm agda (cpair Mt Mu)
| cinl_ Ma : CTerm agda Ma → CTerm agda (cinl Ma)
| cinr_ Mb : CTerm agda Mb → CTerm agda (cinr Mb)

(* in Rocq we have annotated abstractions and pairs, and no ascriptions *)
| clam'_ MA M : CTerm rocq MA -> CTerm rocq M -> CTerm rocq (clam' MA M)
| cpair'_ Mt MB Mu : CTerm rocq Mt -> CTerm rocq MB -> CTerm rocq Mu -> CTerm rocq (cpair' Mt MB Mu)
| iinl_ MB Ma : CTerm rocq MB → CTerm rocq Ma → CTerm rocq (iinl MB Ma)
| iinr_ MA Mb : CTerm rocq MA → CTerm rocq Mb → CTerm rocq (iinr MA Mb)

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
| cJ_ h MP Mp Me : CTerm h MP ->
    CTerm h Mp -> CTerm h Me -> CTerm h (cJ MP Mp Me)
| cLift_ h MA : CTerm h MA -> CTerm h (cLift MA)
| clift_ h Ma : CTerm h Ma -> CTerm h (clift Ma)
| clower_ h Ma : CTerm h Ma -> CTerm h (clower Ma)
| ccast_ h Me Ma : CTerm h Me -> CTerm h Ma -> CTerm h (ccast Me Ma)
| cinjpi1_ h Me : CTerm h Me -> CTerm h (cinjpi1 Me)
| cinjpi2_ h Me Ma : CTerm h Me -> CTerm h Ma -> CTerm h (cinjpi2 Me Ma)
| csum_ h MA MB : CTerm h MA → CTerm h MB → CTerm h (csum MA MB)
| csum_case_ h MP Mpl Mpr Mu :
    CTerm h MP →
    CTerm h Mpl →
    CTerm h Mpr →
    CTerm h Mu →
    CTerm h (csum_case MP Mpl Mpr Mu).

(* auxiliary lemma that only requires us to show the inferring case,
   for the checking case we use the same term *)
Lemma completeness_aux_infer Γ l t T Δ h :
  wt_is_wn ->
  Γ ⊢< l > t : T ->
  ⊢ Γ ≡ Δ ->
  (∃ M U t0,
    (erase_ctx Δ) ⊢< l > M ⇒ (erasure (Ax l) U) ↣ (erasure l t0)
    ∧ Γ ⊢< l > t ≡ t0 : T
    ∧ Γ ⊢< Ax l > T ≡ U : Sort l
    ∧ CTerm h M)
  ->
  (∀ U,
    Γ ⊢< Ax l > T ≡ U : Sort l ->
    exists M t0, (erase_ctx Δ) ⊢< l > M ⇐ (erasure (Ax l) U) ↣ (erasure l t0)
    ∧ Γ ⊢< l > t ≡ t0 : T
    ∧ CTerm h M)
  ∧
  (∃ M U t0,
    (erase_ctx Δ) ⊢< l > M ⇒ (erasure (Ax l) U) ↣ (erasure l t0)
    ∧ Γ ⊢< l > t ≡ t0 : T
    ∧ Γ ⊢< Ax l > T ≡ U : Sort l
    ∧ CTerm h M).
Proof.
  intros wt_is_wn tWt Γ_eq_Δ H.
  split; intros; auto.
  edestruct H as (M & V & t0' & M_infer & t_conv_t0' & T_eq_V & C); eauto.
  assert (Γ ⊢< Ax l > V ≡ U : Sort l) as V_eq_U by eauto using conv_sym, conv_trans.
  apply validity_conv_left in V_eq_U as V_wt.
  apply validity_conv_right in V_eq_U as U_wt.
  apply wt_is_wn in V_wt as (V' & V_redd_V' & nf_V').
  apply wt_is_wn in U_wt as (U' & U_redd_U' & nf_U').
  exists M. eexists. repeat split; eauto using conv_conv.
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
  (exists MT U T0,
      (erase_ctx Δ) ⊢< Ax l > MT ⇒ (erasure (Ax (Ax l)) U) ↣ erasure (Ax l) T0
      ∧ Γ ⊢< Ax l > T ≡ T0 : Sort l
      ∧ Γ ⊢< Ax (Ax l) > Sort l ≡ U : Sort (Ax l)
      ∧ CTerm agda MT) ->
  (forall U,
      Γ ⊢< Ax l > T ≡ U : Sort l ->
      exists M t0, (erase_ctx Δ) ⊢< l > M ⇐ (erasure (Ax l) U) ↣ (erasure l t0)
      ∧ Γ ⊢< l > t ≡ t0 : T ∧ CTerm agda M)
  ->
  (forall U,
      Γ ⊢< Ax l > T ≡ U : Sort l ->
      exists M t0, (erase_ctx Δ) ⊢< l > M ⇐ (erasure (Ax l) U) ↣ (erasure l t0)
      ∧ Γ ⊢< l > t ≡ t0 : T ∧ CTerm agda M)
  ∧
  (exists M U t0,
      (erase_ctx Δ) ⊢< l > M ⇒ (erasure (Ax l) U) ↣ (erasure l t0)
      ∧ Γ ⊢< l > t ≡ t0 : T
      ∧ Γ ⊢< Ax l > T ≡ U : Sort l
      ∧ CTerm agda M).
Proof.
  intros. split; eauto.
  destruct H2 as (MT & U & T0 & MT_infers & T_conv_T0 & sort_conv & CMT).
  edestruct H3 as (M & t0 & M_checks & t_conv_t0 & cM); eauto using validity_ty_ty.
  eapply gen_red in sort_conv; eauto.
  eexists (cann M MT). eexists. eexists.

  repeat split; eauto using validity_ty_ty, conv_refl, CTerm.
  eapply infer_ann; eauto using CTerm, redd_refl.
Qed.


(* we separate the case in the proof for pi, because we reuse it in the
  case for lam, when constructing the type annotation needed for inference *)
Lemma completeness_pi Γ i j A B h :
  wt_is_wn ->
  Γ ⊢< Ax i > A : Sort i ->
  Γ,, (i, A) ⊢< Ax j > B : Sort j ->
  (∀ Δ : ctx, ⊢ Γ ≡ Δ →
      ∃ (M : cterm) (U w : term),
          erase_ctx Δ ⊢< Ax i > M ⇒ erasure (Ax (Ax i)) U ↣ erasure (Ax i) w
          ∧ Γ ⊢< Ax i > A ≡ w : Sort i
          ∧ Γ ⊢< Ax (Ax i) > Sort i ≡ U : Sort (Ax i)
          ∧ CTerm h M) ->
  (∀ Δ : ctx, ⊢ Γ,, (i, A) ≡ Δ →
      ∃ (M : cterm) (U w : term),
          erase_ctx Δ ⊢< Ax j > M ⇒ erasure (Ax (Ax j)) U ↣ erasure (Ax j) w
          ∧ Γ,, (i, A) ⊢< Ax j > B ≡ w : Sort j
          ∧ Γ,, (i, A) ⊢< Ax (Ax j) > Sort j ≡ U : Sort (Ax j)
          ∧ CTerm h M) ->
  forall Δ, ⊢ Γ ≡ Δ ->
  ∃ (M : cterm) (U w : term),
      erase_ctx Δ ⊢< Ax (Ru i j) > M ⇒ erasure (Ax (Ax (Ru i j))) U ↣ erasure (Ax (Ru i j)) w
      ∧ Γ ⊢< Ax (Ru i j) > Pi i j A B ≡ w : Sort (Ru i j)
      ∧ Γ ⊢< Ax (Ax (Ru i j)) > Sort (Ru i j) ≡ U : Sort (Ax (Ru i j))
      ∧ CTerm h M.
Proof.
  intros wt_is_wn A_Wt B_Wt HA HB Δ Γ_eq_Δ.
  edestruct HA as (MA & UA & wA & MA_infer & A_conv_wA & sort_eq_UA & CA); eauto.
  eapply gen_red in sort_eq_UA; eauto.

  edestruct HB as (MB & UB & wB & MB_infer & B_conv_wB & sort_eq_UB & CB); eauto using conv_ccons, conv_refl.
  eapply gen_red in sort_eq_UB; eauto.

  exists (cPi MA MB). exists (Sort (Ru i j)). exists (Pi i j wA wB).
  repeat split; eauto using CTerm, conv_sort, validity_ty_ctx, conv_pi, validity_conv_left.
  eapply infer_pi; eauto.
Qed.

Lemma completeness_Sigma Γ n m A B h :
  wt_is_wn ->
  Γ ⊢< Ax (ty n) > A : Sort (ty n) ->
  Γ,, (ty n, A) ⊢< Ax (ty m) > B : Sort (ty m) ->
  (∀ Δ : ctx, ⊢ Γ ≡ Δ ->
      ∃ (M : cterm) (U w : term),
          erase_ctx Δ ⊢< Ax (ty n) > M ⇒ erasure (Ax (Ax (ty n))) U ↣ erasure (Ax (ty n)) w
          ∧ Γ ⊢< Ax (ty n) > A ≡ w : Sort (ty n)
          ∧ Γ ⊢< Ax (Ax (ty n)) > Sort (ty n) ≡ U : Sort (Ax (ty n)) ∧ CTerm h M) ->

  (∀ Δ : ctx, ⊢ Γ,, (ty n, A) ≡ Δ ->
      ∃ (M : cterm) (U w : term),
          erase_ctx Δ ⊢< Ax (ty m) > M ⇒ erasure (Ax (Ax (ty m))) U ↣ erasure (Ax (ty m)) w
          ∧ Γ,, (ty n, A) ⊢< Ax (ty m) > B ≡ w : Sort (ty m)
          ∧ Γ,, (ty n, A) ⊢< Ax (Ax (ty m)) > Sort (ty m) ≡ U : Sort (Ax (ty m)) ∧ CTerm h M) ->
  forall Δ, ⊢ Γ ≡ Δ ->
  ∃ (M : cterm) (U w : term),
      erase_ctx Δ ⊢< Ax (ty (max n m)) > M ⇒ erasure (Ax (Ax (ty (max n m)))) U ↣ erasure (Ax (ty (max n m))) w
      ∧ Γ ⊢< Ax (ty (max n m)) > Sigma (ty n) (ty m) A B ≡ w : Sort (ty (max n m))
      ∧ Γ ⊢< Ax (Ax (ty (max n m))) > Sort (ty (max n m)) ≡ U : Sort (Ax (ty (max n m)))
      ∧ CTerm h M.
Proof.
  intros wt_is_wn A_Wt B_Wt HA HB Δ Γ_eq_Δ.
  edestruct HA as (MA & UA & A0 & MA_infer & A_conv_A0 & sort_eq_UA & CA); eauto.
  eapply gen_red in sort_eq_UA; eauto. clear HA.

  edestruct HB as (MB & UB & B0 & MB_infer & B_conv_B0 & sort_eq_UB & CB); eauto using conv_ccons, conv_refl. clear HB.
  eapply gen_red in sort_eq_UB; eauto.

  exists (cSigma MA MB). eexists. exists (Sigma (ty n) (ty m) A0 B0).
  repeat split; eauto using CTerm, conv_sort, validity_ty_ctx.
  eapply infer_sigma; eauto.
  econstructor; eauto.
Qed.

Lemma completeness_sum Γ n m A B h :
  wt_is_wn →
  Γ ⊢< Ax (ty n) > A : Sort (ty n) →
  Γ ⊢< Ax (ty m) > B : Sort (ty m) →
  (∀ Δ : ctx,
    ⊢ Γ ≡ Δ →
    ∃ (M : cterm) (U w : term),
      erase_ctx Δ ⊢< Ax (ty n) > M ⇒ erasure (Ax (Ax (ty n))) U ↣ erasure (Ax (ty n)) w ∧
      Γ ⊢< Ax (ty n) > A ≡ w : Sort (ty n) ∧
      Γ ⊢< Ax (Ax (ty n)) > Sort (ty n) ≡ U : Sort (Ax (ty n)) ∧
      CTerm h M
  ) →
  (∀ Δ : ctx,
    ⊢ Γ ≡ Δ →
    ∃ (M : cterm) (U w : term),
      erase_ctx Δ ⊢< Ax (ty m) > M ⇒ erasure (Ax (Ax (ty m))) U ↣ erasure (Ax (ty m)) w ∧
      Γ ⊢< Ax (ty m) > B ≡ w : Sort (ty m) ∧
      Γ ⊢< Ax (Ax (ty m)) > Sort (ty m) ≡ U : Sort (Ax (ty m)) ∧
      CTerm h M
  ) →
  ∀ Δ,
    ⊢ Γ ≡ Δ →
    ∃ (M : cterm) (U w : term),
      erase_ctx Δ ⊢< Ax (ty (max n m)) > M ⇒ erasure (Ax (Ax (ty (max n m)))) U ↣ erasure (Ax (ty (max n m))) w ∧
      Γ ⊢< Ax (ty (max n m)) > tysum (ty n) (ty m) A B ≡ w : Sort (ty (max n m)) ∧
      Γ ⊢< Ax (Ax (ty (max n m))) > Sort (ty (max n m)) ≡ U : Sort (Ax (ty (max n m))) ∧
      CTerm h M.
Proof.
  intros wt_is_wn A_Wt B_Wt HA HB Δ Γ_eq_Δ.
  edestruct HA as (MA & UA & A0 & MA_infer & A_conv_A0 & sort_eq_UA & CA); eauto.
  eapply gen_red in sort_eq_UA; eauto. clear HA.

  edestruct HB as (MB & UB & B0 & MB_infer & B_conv_B0 & sort_eq_UB & CB); eauto.
  clear HB.
  eapply gen_red in sort_eq_UB; eauto.

  eexists (csum MA MB), _, (tysum (ty n) (ty m) A0 B0).
  repeat split; eauto using CTerm, conv_sort, validity_ty_ctx.
  - eapply infer_sum; eauto.
  - econstructor; eauto.
Qed.

Lemma completeness_Lift Γ i A h :
  wt_is_wn ->
  Γ ⊢< Ax i > A : Sort i ->
  (∀ Δ : ctx, ⊢ Γ ≡ Δ →
      ∃ (M : cterm) (U A0 : term),
          erase_ctx Δ ⊢< Ax i > M ⇒ erasure (Ax (Ax i)) U ↣ erasure (Ax i) A0
          ∧ Γ ⊢< Ax i > A ≡ A0 : Sort i
          ∧ Γ ⊢< Ax (Ax i) > Sort i ≡ U : Sort (Ax i)
          ∧ CTerm h M) ->
  forall Δ, ⊢ Γ ≡ Δ ->
  ∃ (M : cterm) (U A0 : term),
      erase_ctx Δ ⊢< Ax (Ax i) > M ⇒ erasure (Ax (Ax (Ax i))) U ↣ erasure (Ax (Ax i)) A0
      ∧ Γ ⊢< Ax (Ax i) > Lift i A ≡ A0 : Sort (Ax i)
      ∧ Γ ⊢< Ax (Ax (Ax i)) > Sort (Ax i) ≡ U : Sort (Ax (Ax i))
      ∧ CTerm h M.
Proof.
  intros wt_is_wn A_Wt HA Δ Γ_eq_Δ.
  edestruct HA as (MA & UA & A0 & MA_infer & A_conv_A0 & sort_eq_UA & CA); eauto.
  eapply gen_red in sort_eq_UA; eauto.

  exists (cLift MA). exists (Sort (Ax i)). exists (Lift i A0).
  repeat split; eauto using CTerm, conv_sort, validity_ty_ctx.
  eapply infer_Lift; eauto.
  econstructor; eauto.
Qed.

Lemma eq_redd l A A' a a' b b' :
  A -->> A' ->
  a -->> a' ->
  b -->> b' ->
  Eq l A a b -->> Eq l A' a' b'.
Proof.
  intros.
  eapply (redd_trans _ _ (Eq l A' a b)).
  2:eapply (redd_trans _ _ (Eq l A' a' b)).
  - clear H0 H1. induction H; eauto using red, redd.
  - clear H H1. induction H0; eauto using red, redd.
  - clear H0 H. induction H1; eauto using red, redd.
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
    exists M t0, (erase_ctx Δ) ⊢< l > M ⇐ (erasure (Ax l) U) ↣ (erasure l t0)
    ∧ Γ ⊢< l > t ≡ t0 : T
    ∧ CTerm h M)
  ∧
  (exists M U t0,
    (erase_ctx Δ) ⊢< l > M ⇒ (erasure (Ax l) U) ↣ (erasure l t0)
    ∧ Γ ⊢< l > t ≡ t0 : T
    ∧ Γ ⊢< Ax l > T ≡ U : Sort l
    ∧ CTerm h M).
Proof.
  intros wt_is_wn Wt.
  pose proof Wt as Wt'.
  generalize Δ. clear Δ.
  induction Wt;intros.

  (* case var *)
  - eapply completeness_aux_infer; eauto.
    eapply conv_in_ctx_ty in Wt'; eauto.
    eapply type_inv in Wt'. dependent destruction Wt'.
    exists (cvar x). eexists. exists (var x).
    repeat split; eauto using CTerm.
    + eapply infer_var. apply varty_erase. eassumption.
    + eapply conv_in_ctx_conv; eauto using ctx_conv_sym, conv_var, validity_ctx_conv_right, conv_conv, conv_sym.
    + eapply conv_in_ctx_conv; eauto using ctx_conv_sym.

  (* case sort *)
  - eapply completeness_aux_infer; eauto.
    exists (cSort l). exists (Sort (Ax l)). exists (Sort l).
    split; eauto using CTerm, conv_refl, validity_ty_ty, infer_Sort, conv_sort.

  (* case pi *)
  - eapply completeness_aux_infer; eauto.
    eapply completeness_pi; eauto. apply IHWt1; eauto. apply IHWt2; eauto.

  (* case lam *)
  - destruct h.
      + eapply completeness_aux_check; eauto.
        * eapply completeness_pi; eauto. apply IHWt1; eauto. apply IHWt2; eauto.
        * intros. clear IHWt1 IHWt2.
          eapply gen_red in H0 as (A' & B' & A_eq_A' & B_eq_B' & U_red_pi); eauto.
          edestruct IHWt3 as ((Mt & t0 & Mt_check & t_conv_t0 & Ct) & _); eauto using conv_ccons, conv_refl. clear IHWt3.
          exists (clam Mt). eexists (lam i j A B t0). repeat split; eauto using CTerm, conv_refl, conv_lam, validity_conv_left.
          erewrite lam_box_erasure; eauto using validity_conv_right.
          eapply check_lam. apply U_red_pi. eauto.

      +   apply completeness_aux_infer; eauto. clear IHWt2.
          edestruct IHWt1 as (_ & MA & UA & A0 & MA_infer & A_conv_A0 & sort_eq_UA & CA); eauto. clear IHWt1.
          eapply gen_red in sort_eq_UA; eauto.

          edestruct IHWt3 as (_ & Mt & B' & t0  & Mt_infer & t_conv_t0 & B_eq_B' & CM); eauto using conv_ccons, conv_refl. clear IHWt3.

          exists (clam' MA Mt). exists (Pi i j A0 B').
          exists (lam i j A0 B' t0).
          repeat split; eauto using CTerm.
          ++ erewrite lam_box_erasure; eauto using validity_conv_right.
              eapply infer_lam; eauto.
          ++ econstructor; eauto.
          ++ eauto using conv_pi, conv_refl.

  (* case app *)
  - eapply completeness_aux_infer; eauto. clear IHWt1 IHWt2.
    edestruct IHWt3 as (_ & Mt & UA & t0 & Mr_infer & t_conv_t0 & pi_eq_UA & Ct); eauto. clear IHWt3.
    eapply gen_red in pi_eq_UA as (A' & B' & A_eq_A' & B_eq_B' & erasure_UA_red); eauto.

    edestruct IHWt4 as ((Mu & u0 & Mu_check & u_conv_u0 & Cu) & _); eauto. clear IHWt4.

    exists (capp Mt Mu). eexists (B' <[ u0 ..]).
    exists (app i j A' B' t0 u0).
    repeat split; eauto using CTerm.
    + erewrite app_box_erasure; eauto using validity_conv_right.
      erewrite erasure_subst_1_commutes; eauto using validity_conv_right.
      eapply infer_app; eauto.
    + econstructor; eauto.
    + eapply subst_conv; eauto using substs_one, validity_ty_ctx.



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
          edestruct IHWt3 as ((Mt & t0 & Mt_check & t_conv_t0 & Ct) & _); eauto.
          edestruct IHWt4 as ((Mu & u0 & Mu_check & u_conv_u0 & Cu) & _); eauto.
          1:eapply subst_conv; eauto using validity_ty_ctx, substs_one, conv_refl.
          clear IHWt3 IHWt4.
          erewrite erasure_subst_1_commutes in Mu_check; eauto using validity_conv_right.
          exists (cpair Mt Mu). exists (pair (ty n') (ty m') A' B' t0 u0).
          repeat split; eauto using CTerm.
          simpl. eapply check_pair; eauto.
          econstructor; eauto.

      +   apply completeness_aux_infer; eauto. clear IHWt1.
          edestruct IHWt3 as (_ & Ma & A' & a0 & Ma_infer & a_conv_a0 & A_conv_A' & Ca); eauto.

          edestruct IHWt2 as (_ & MB & UB & B0 & MB_infer & B_conv_B0 & sort_eq_UB & CB); eauto using  conv_ccons.
          eapply gen_red in sort_eq_UB; eauto. clear IHWt3 IHWt2.

          edestruct IHWt4 as ((Mb & b0 & Mb_check & b_conv_b0 & Cb) & _).
          1,2:eauto using conv_refl, validity_ty_ty.
          1:eapply subst_conv; eauto using substs_one, validity_ty_ctx.
          clear IHWt4.
          erewrite erasure_subst_1_commutes in Mb_check; eauto using validity_conv_right.

          exists (cpair' Ma MB Mb). exists (Sigma (ty n) (ty m) A' B0).
          exists (pair (ty n) (ty m) A' B0 a0 b0).
          repeat split; eauto using CTerm.
          ++ simpl. eapply infer_pair; eauto.
          ++ econstructor; eauto.
          ++ eauto using conv_sigma, conv_refl.

  (* case pi1 *)
  - eapply completeness_aux_infer; eauto. clear IHWt1 IHWt2.
    edestruct IHWt3 as (_ & Mt & UA & t0 & Mr_infer & t_conv_t0 & sig_eq_UA & Ct); eauto.
    eapply gen_red in sig_eq_UA as (A' & B' & n' & m' & eq1 & eq2 & A_eq_A' & B_eq_B' & erasure_UA_red); eauto. clear IHWt3.
    ty_inj_tac. subst.

    exists (cpi1 Mt). eexists. exists (pi1 (ty n') (ty m') A' B' t0).
    repeat split; eauto using CTerm.
    simpl. econstructor; eauto.
    econstructor;eauto.

  (* case pi2 *)
  - eapply completeness_aux_infer; eauto. clear IHWt1 IHWt2.
    edestruct IHWt3 as (_ & Mt & UA & t0 & Mr_infer & t_conv_t0 & sig_eq_UA & Ct); eauto.
    eapply gen_red in sig_eq_UA as (A' & B' & n' & m' & eq1 & eq2 & A_eq_A' & B_eq_B' & erasure_UA_red); eauto. clear IHWt3.
    ty_inj_tac. subst.

    exists (cpi2 Mt). eexists. exists (pi2 (ty n') (ty m') A' B' t0).
    repeat split; eauto using CTerm; simpl.
    3:{eapply subst_conv; eauto using validity_ty_ctx.
        eapply substs_one; econstructor; eauto. }
    erewrite erasure_subst_1_commutes; eauto using validity_conv_right.
    eapply infer_pi2; eauto.
    econstructor; eauto.

  (* case nat *)
  - eapply completeness_aux_infer; eauto.
    exists cNat. exists (Sort (ty 0)). exists Nat.
    intuition eauto using conv_refl, validity_ty_ty, infer_Nat, CTerm.

  (* case zero *)
  - eapply completeness_aux_infer; eauto.
    exists czero. exists Nat. exists zero.
    intuition eauto using conv_refl, validity_ty_ty, infer_zero, CTerm.

  (* case succ *)
  - eapply completeness_aux_infer; eauto.
    edestruct IHWt as ((Mt & t0 & Mt_check & t_conv_t0 & Ct) & _); eauto using validity_ty_ty, conv_refl.
    exists (csucc Mt). exists Nat. exists (succ t0).
    intuition eauto using conv_refl, validity_ty_ty, infer_succ, CTerm, conversion.

  (* case rec *)
  - eapply completeness_aux_infer; eauto.
    edestruct IHWt1 as (_ & MP & U & P0 & MP_infer & P_conv_P0 & sort_eq_U & CP); eauto using conv_ccons, conv_nat, validity_ty_ctx. clear IHWt1.
    eapply gen_red in sort_eq_U; eauto.

    edestruct IHWt2 as ((Mp_zero & p_zero0 & Mp_zero_check & p_zero_conv_p_zero0 & Cp_zero) & _); eauto 6 using subst_conv, substs_one, conv_zero, validity_ty_ctx.
    clear IHWt2.

    edestruct IHWt3 as ((Mp_succ & p_succ0 & Mp_succ_check & p_succ_conv_p_succ0 & Cp_succ) & _); eauto 7 using conv_ccons, conv_nat, conv_nat, validity_ty_ctx.
    eapply subst_conv; eauto using validity_ty_ctx, subst_id_var1, refl_subst.
    clear IHWt3.

    edestruct IHWt4 as ((Mt & t0 & Mt_check & t_conv_t0 & Ct) & _); eauto using conv_refl, validity_ty_ty. clear IHWt4.

    exists (crec MP Mp_zero Mp_succ Mt). exists (P0 <[ t0 ..]).
    exists (rec l P0 p_zero0 p_succ0 t0).
    intuition eauto using validity_ty_ty, CTerm.
    + erewrite erasure_subst_1_commutes; eauto using validity_conv_right.
      eapply infer_rec; eauto; fold erasure.
      * erewrite erasure_subst_1_commutes in Mp_zero_check; eauto using validity_conv_right. eauto.
      * erewrite aux_subst_commute in Mp_succ_check; eauto using validity_conv_right.
    + econstructor; eauto.
    + eapply subst_conv; eauto using substs_one, validity_ty_ctx.

  (* case Eq *)
  - eapply completeness_aux_infer; eauto.
    edestruct IHWt1 as (_ & MA & UA & A0 & MA_infer & A_conv_A0 & sort_eq_UA & CA); eauto.
    eapply gen_red in sort_eq_UA; eauto. clear IHWt1.

    edestruct IHWt2 as ((Ma & a0 & Ma_checks & a_conv_a0 & Ca) & _); eauto using conv_refl.
    edestruct IHWt3 as ((Mb & b0 & Mb_checks & b_conv_b0 & Cb) & _); eauto using conv_refl.

    eexists (cEq MA Ma Mb). eexists (Sort prop). exists (Eq l A0 a0 b0).
    intuition eauto using CTerm, conv_sort, validity_ty_ctx.
    simpl. eapply infer_eq; eauto.
    econstructor; eauto.

  (* case J *)
  - eapply completeness_aux_infer; eauto.
    clear IHWt1 IHWt2 IHWt5.

    edestruct IHWt6 as (_ & Me & UA & e0 & Me_infer & e_conv_e0 & Eq_eq_UA & Ce); eauto. clear IHWt6.
    eapply gen_red in Eq_eq_UA as (A' & a' & b' & A_conv_A' & a_conv_a' & b_conv_b' & erasure_UA_red ); eauto.

    edestruct IHWt3 as (_ & MP & UP & P0 & MP_infer & P_conv_P0 & sort_eq_UP & CP); eauto  using ConvCtx.
    eapply gen_red in sort_eq_UP; eauto. clear IHWt3.

    edestruct IHWt4 as ((Mp & p0 & Mp_checks & p_conv_p0 & Cp) & _); eauto using subst_conv, substs_one, validity_ty_ctx.
    clear IHWt4.

    exists (cJ MP Mp Me).
    exists (P0 <[b'..]).
    exists (J l i A' a' P0 p0 b' e0).
    intuition eauto using CTerm.
    + erewrite erasure_subst_1_commutes; eauto using validity_conv_right.
      simpl. eapply infer_J; eauto.
      * rewrite erasure_prop in Me_infer; eauto.
      * erewrite erasure_subst_1_commutes in Mp_checks; eauto using validity_conv_right.
    + econstructor; eauto.
    + eapply subst_conv; eauto using substs_one, validity_ty_ctx.

  (* case Lift *)
  - eapply completeness_aux_infer; eauto.
    eapply completeness_Lift; eauto.  intros. eapply IHWt; eauto.


  (* case lift *)
  - destruct h.
    + eapply completeness_aux_check; eauto.
      * eapply completeness_Lift; eauto. eapply IHWt1; eauto.

      * intros.
        eapply gen_red in H0 as (A' & A_eq_A' & erasure_UA_red); eauto.
        edestruct IHWt2 as (H' & _); eauto. clear IHWt1 IHWt2.
        eapply H' in A_eq_A' as temp.
        destruct temp as (M & a0 & M_checks & a_conv_a0 & CM).
        exists (clift M). exists (lift l A' a0).
        intuition eauto using CTerm.
        eapply check_lift; eauto.
        econstructor; eauto.

    + eapply completeness_aux_infer; eauto.
      edestruct IHWt2 as (_ & Ma & UA & a0 & Mr_infer & a_conv_a0 & Lift_eq_UA & Ca); eauto. clear IHWt1 IHWt2.
      exists (clift Ma). eexists. exists (lift l UA a0).
      repeat split; eauto using CTerm.
      3:eauto using conv_Lift.
      simpl. eapply infer_lift; eauto.
      econstructor;eauto.

  (* case lower *)
  - eapply completeness_aux_infer; eauto.
    edestruct IHWt2 as (_ & Mt & UA & t0 & Mr_infer & t_conv_t0 & Lift_eq_UA & Ct); eauto. clear IHWt1 IHWt2.
    eapply gen_red in Lift_eq_UA as (A' & A_eq_A' & erasure_UA_red); eauto.

    exists (clower Mt). eexists. exists (lower l A' t0).
    repeat split; eauto using CTerm.
    eapply infer_lower; eauto.
    econstructor; eauto.

    (* case cast *)
    - eapply completeness_aux_infer; eauto.  clear IHWt1 IHWt2.
    edestruct IHWt3 as (_ & Me & UA & e0 & Me_infer & e_conv_e0 & Eq_eq_UA & Ce); eauto. clear IHWt3.
    eapply gen_red in Eq_eq_UA as (_sort & A' & B' & sort_conv_sort & A_conv_A' & B_conv_B' & erasure_UA_red); eauto.
    eapply gen_red in sort_conv_sort; eauto.

    assert (erasure (Ax prop) UA -->> Eq (Ax i) (Sort i) (erasure (Ax i) A')
(erasure (Ax i) B')) by eauto using redd_trans, eq_redd, redd_refl.

    edestruct IHWt4 as ((Ma & a0 & Ma_check & a_conv_a0 & Ca) & _); eauto. clear IHWt4.
    exists (ccast Me Ma). exists B'. eexists (cast i A' B' e0 a0).
    repeat split; eauto using CTerm.
    eapply infer_cast; eauto; fold erasure.
    econstructor; eauto.

    (* case injpi1 *)
  - eapply completeness_aux_infer; eauto.
    clear IHWt1 IHWt2 IHWt3 IHWt4.
    edestruct IHWt5 as (_ & Me & UA & e0 & Me_infer & e_conv_e0 & Eq_eq_UA & Ce); eauto. clear IHWt5.
    eapply gen_red in Eq_eq_UA as (_sort & V1 & V2 & sort_conv & Pi1_conv & Pi2_conv & erasure_UA_red ); eauto.
    eapply gen_red in sort_conv; eauto.

    eapply gen_red in Pi1_conv as (A1' & B1' & A1_conv_A1' & B1_conv_B1' & erasure_Pi1); eauto.

    eapply gen_red in Pi2_conv as (A2' & B2' & A2_conv_A2' & B2_conv_B2' & erasure_Pi2); eauto.

    assert (erasure (Ax prop) UA -->> Eq (Ax (Ru i (ty n))) (Sort (Ru i (ty n))) (Pi i (ty n) (erasure (Ax i) A1') (erasure (Ax (ty n)) B1')) (Pi i (ty n) (erasure (Ax i) A2') (erasure (Ax (ty n)) B2')))  by eauto using redd_trans, eq_redd, redd_refl.

    clear erasure_UA_red erasure_Pi1 erasure_Pi2 sort_conv.

    exists (cinjpi1 Me). exists (Eq (Ax i) (Sort i) A2' A1').
    exists (injpi1 i (ty n) A1' A2' B1' B2' e0).
    repeat split; eauto using CTerm.
    + eapply infer_injpi1; eauto.
    + econstructor; eauto.
    + econstructor; eauto using conv_sort, validity_ty_ctx.

    (* case injpi2 *)
  - eapply completeness_aux_infer; eauto.
    clear IHWt1 IHWt2 IHWt3 IHWt4.
    edestruct IHWt5 as (_ & Me & UA & e0 & Me_infer & e_conv_e0 & Eq_eq_UA & Ce); eauto. clear IHWt5.
    eapply gen_red in Eq_eq_UA as (_sort & V1 & V2 & sort_conv & Pi1_conv & Pi2_conv & erasure_UA_red ); eauto.
    eapply gen_red in sort_conv; eauto.

    eapply gen_red in Pi1_conv as (A1' & B1' & A1_conv_A1' & B1_conv_B1' & erasure_Pi1); eauto.

    eapply gen_red in Pi2_conv as (A2' & B2' & A2_conv_A2' & B2_conv_B2' & erasure_Pi2); eauto.

    assert (erasure (Ax prop) UA -->> Eq (Ax (Ru i (ty n))) (Sort (Ru i (ty n))) (Pi i (ty n) (erasure (Ax i) A1') (erasure (Ax (ty n)) B1')) (Pi i (ty n) (erasure (Ax i) A2') (erasure (Ax (ty n)) B2')))  by eauto using redd_trans, eq_redd, redd_refl.

    clear erasure_UA_red erasure_Pi1 erasure_Pi2 sort_conv.

    edestruct IHWt6 as ((Ma & a20 & Ma_check & a2_conv_a20 & Ca) & _); eauto.
    clear IHWt6.

    pose (a10 := cast i A2' A1' (injpi1 i (ty n) A1 A2 B1 B2 e) a20).

    exists (cinjpi2 Me Ma).
    exists (Eq (Ax (ty n)) (Sort (ty n)) (B1'<[a10..]) (B2' <[a20..])).
    exists (injpi2 i (ty n) A1' A2' B1' B2' e0 a20).
    repeat split; eauto using CTerm.
    + simpl.
      erewrite erasure_subst_1_commutes; eauto using validity_conv_right.
      erewrite erasure_subst_1_commutes; eauto using validity_conv_right.
      eapply infer_injpi2; eauto; fold erasure.
    + econstructor; eauto.
    + econstructor; eauto using conv_sort, validity_ty_ctx.
      all:eapply subst_conv; eauto using validity_ty_ctx.
      all:eapply substs_one; eauto.
      unfold_all_local. econstructor; eauto using conv_refl, typing.

  (* sum *)
  - eapply completeness_aux_infer ; eauto.
    eapply completeness_sum ; eauto.
    + apply IHWt1; eauto.
    + apply IHWt2; eauto.

  (* inl *)
  - destruct h.
    + eapply completeness_aux_check; eauto.
      * eapply completeness_sum ; eauto.
        -- apply IHWt1; eauto.
        -- apply IHWt2; eauto.
      * intros. clear IHWt1 IHWt2.
        eapply gen_red in H0 as (A' & B' & n' & m' & eq1 & eq2 & A_eq_A' & B_eq_B' & U_red_pi); eauto.
        ty_inj_tac. subst.
        edestruct IHWt3 as ((Ma & a0 & Ma_check & a_conv_a0 & Ca) & _); eauto.
        clear IHWt3.
        exists (cinl Ma), (inl (ty n') (ty m') A' B' a0).
        repeat split; eauto using CTerm.
        -- simpl. eapply check_inl; eauto.
        -- econstructor; eauto.

    + apply completeness_aux_infer; eauto. clear IHWt1.
      edestruct IHWt3 as (_ & Ma & A' & a0 & Ma_infer & a_conv_a0 & A_conv_A' & Ca); eauto.

      edestruct IHWt2 as (_ & MB & UB & B0 & MB_infer & B_conv_B0 & sort_eq_UB & CB); eauto using conv_ccons.
      eapply gen_red in sort_eq_UB; eauto. clear IHWt3 IHWt2.

      exists (iinl MB Ma), (tysum (ty i) (ty j) A' B0).
      exists (inl (ty i) (ty j) A' B0 a0).
      repeat split; eauto using CTerm.
      -- simpl. eapply infer_inl; eauto.
      -- econstructor; eauto.
      -- eauto using conv_sum, conv_refl.

  (* inr *)
  - destruct h.
    + eapply completeness_aux_check; eauto.
      * eapply completeness_sum ; eauto.
        -- apply IHWt1; eauto.
        -- apply IHWt2; eauto.
      * intros. clear IHWt1 IHWt2.
        eapply gen_red in H0 as (A' & B' & n' & m' & eq1 & eq2 & A_eq_A' & B_eq_B' & U_red_pi); eauto.
        ty_inj_tac. subst.
        edestruct IHWt3 as ((Ma & a0 & Ma_check & a_conv_a0 & Ca) & _); eauto.
        clear IHWt3.
        exists (cinr Ma), (inr (ty n') (ty m') A' B' a0).
        repeat split; eauto using CTerm.
        -- simpl. eapply check_inr; eauto.
        -- econstructor; eauto.

    + apply completeness_aux_infer; eauto. clear IHWt2.
      edestruct IHWt3 as (_ & Mb & B' & b0 & Mb_infer & b_conv_b0 & B_conv_B' & Cb); eauto.

      edestruct IHWt1 as (_ & MA & UA & A0 & MA_infer & A_conv_A0 & sort_eq_UA & CA); eauto using conv_ccons.
      eapply gen_red in sort_eq_UA; eauto. clear IHWt3 IHWt1.

      exists (iinr MA Mb), (tysum (ty i) (ty j) A0 B').
      exists (inr (ty i) (ty j) A0 B' b0).
      repeat split; eauto using CTerm.
      -- simpl. eapply infer_inr; eauto.
      -- econstructor; eauto.
      -- eauto using conv_sum, conv_refl.

  (* sum_case *)
  - eapply completeness_aux_infer ; eauto.

    edestruct IHWt6 as (_ & Mt & Tt & t' & ht & et & eTt & Ct). all: eauto.
    eapply gen_red in eTt as (A' & B' & n & m & ? & ? & eA & eB & rTt). 2: eauto.
    ty_inj_tac. subst. clear IHWt6.

    edestruct IHWt3 as (_ & MP & TP & P' & hP & eP & eTP & CP).
    all: eauto using conv_ccons, conv_sum.
    eapply gen_red in eTP. all: eauto.
    clear IHWt3.

    edestruct IHWt4 as ((Mpl & pl' & hpl & epl & Cpl) & _).
    all: eauto using conv_ccons.
    1:{
      eapply subst_conv. all: eauto with sidecond.
      apply refl_subst. apply well_scons_alt.
      1: eauto with sidecond.
      rasimpl. econstructor.
      all: eauto using type_ren, validity_conv_left with sidecond.
      econstructor. all: eauto with sidecond.
    }
    clear IHWt4.

    edestruct IHWt5 as ((Mpr & pr' & hpr & epr & Cpr) & _).
    all: eauto using conv_ccons.
    1:{
      eapply subst_conv. all: eauto with sidecond.
      apply refl_subst. apply well_scons_alt.
      1: eauto with sidecond.
      rasimpl. econstructor.
      all: eauto using type_ren, validity_conv_left with sidecond.
      econstructor. all: eauto with sidecond.
    }
    clear IHWt5.

    exists (csum_case MP Mpl Mpr Mt), (P' <[ t' ..]).
    exists (sum_case (ty n) (ty m) l A' B' P' pl' pr' t').
    intuition eauto using validity_ty_ty, CTerm.
    + erewrite erasure_subst_1_commutes; eauto using validity_conv_right.
      eapply infer_sum_case; eauto; fold erasure.
      * erewrite inl_subst_comm in hpl; eauto using validity_conv_right.
      * erewrite inr_subst_comm in hpr; eauto using validity_conv_right.
    + econstructor; eauto.
    + eapply subst_conv; eauto using substs_one, validity_ty_ctx.

  (* case conv *)
  - eapply IHWt in H0 as (IH_check & IH_infer); eauto. clear IHWt. split; intros.
    + assert (Γ ⊢< Ax l > A ≡ U : Sort l) as A_eq_U by eauto using conv_sym, conv_trans.
      eapply IH_check in A_eq_U as (M & t0 & M_check & t_conv_t0 & CM).
      intuition eauto 7 using conv_conv.
    + destruct IH_infer as (M & U & t0 & M_infer & t_conv_t0 & B_eq_U & CM).
      assert (Γ ⊢< Ax l > A ≡ U : Sort l) as A_eq_U by eauto using conv_sym, conv_trans.
      intuition eauto 12 using conv_conv, conv_sym, conv_trans.
Qed.

Corollary completeness_check Γ l t T h :
  wt_is_wn -> Γ ⊢< l > t : T ->
  exists M t',
    (erase_ctx Γ) ⊢< l > M ⇐ (erasure (Ax l) T) ↣ (erasure l t')
    ∧ Γ ⊢< l > t ≡ t' : T ∧ CTerm h M.
Proof.
  intros. pose proof H0 as Wt.
  eapply completeness in Wt as (case_check & case_infer);
  eauto using ctx_conv_refl, validity_ty_ctx.
  eapply case_check. eauto using validity_ty_ty, conv_refl.
Qed.

Corollary completeness_infer Γ l t T h :
  wt_is_wn -> Γ ⊢< l > t : T ->
  exists M U t', (erase_ctx Γ) ⊢< l > M ⇒ (erasure (Ax l) U) ↣ (erasure l t')
      ∧ Γ ⊢< l > t ≡ t' : T ∧ Γ ⊢< Ax l > T ≡ U : Sort l  ∧ CTerm h M.
Proof.
  intros. pose proof H0 as Wt.
  eapply completeness in Wt as (case_check & case_infer);
  eauto using ctx_conv_refl, validity_ty_ctx.
Qed.


Print Assumptions completeness_infer.
