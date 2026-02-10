(** * Typing *)

From Stdlib Require Import Utf8 List Arith Bool.
From TypedConfluence
Require Import core unscoped Ast SubstNotations RAsimpl AST_rasimpl.
From TypedConfluence Require Import Util BasicAST Contexts.
From Stdlib Require Import Setoid Morphisms Relation_Definitions.

Import ListNotations.
Import CombineNotations.

Set Default Goal Selector "!".

Open Scope subst_scope.



Definition Ax (l : level) : level :=
  ty (match l with
  | prop => 0
  | ty i => S i
  end).

Definition Ru (l1 l2 : level) : level :=
  match l2 with
  | prop => prop
  | ty j => ty (match l1 with | prop => j | ty i => max i j end)
  end.

Reserved Notation "Γ ∋< l > x : T" (at level 50, l, x, T at next level).
Reserved Notation "Γ ⊢< l > t : T" (at level 50, l, t, T at next level).
Reserved Notation "Γ ⊢< l > t ≡ u : T" (at level 50, l, t, u, T at next level).
Reserved Notation "⊢ Γ" (at level 50).

Inductive varty : ctx → nat → level → term → Prop :=
| vartyO Γ l A : Γ ,, (l , A) ∋< l > 0 : S ⋅ A
| vartyS Γ i j A B x : Γ ∋< i > x : A → Γ ,, (j, B) ∋< i > S x : S ⋅ A

where "Γ ∋< l > x : T" := (varty Γ x l T).
(*
1 - 11 : ok
12 - 23 : +3
24 - 29 : +6
30 - 31 : +8
*)

Inductive typing : ctx -> level -> term → term → Prop :=

| type_var :
    ∀ Γ x l A,
      ⊢ Γ →
      Γ ∋< l > x : A →
      Γ ⊢< l > var x : A

| type_sort :
    ∀ Γ l,
      ⊢ Γ →
      Γ ⊢< Ax (Ax l) > Sort l : Sort (Ax l)

(* Dependent functions *)

| type_pi :
    ∀ Γ i j A B,
      Γ ⊢< Ax i > A : Sort i →
      Γ ,, (i , A) ⊢< Ax j > B : Sort j →
      Γ ⊢< Ax (Ru i j) > Pi i j A B : Sort (Ru i j)

| type_lam :
    ∀ Γ i j A B t,
      Γ ⊢< Ax i > A : Sort i →
      Γ ,, (i , A) ⊢< Ax j > B : Sort j →
      Γ ,, (i , A) ⊢< j > t : B →
      Γ ⊢< Ru i j > lam i j A B t : Pi i j A B

| type_app :
    ∀ Γ i j A B t u,
      Γ ⊢< Ax i > A : Sort i →
      Γ ,, (i , A) ⊢< Ax j > B : Sort j →
      Γ ⊢< Ru i j > t : Pi i j A B →
      Γ ⊢< i > u : A →
      Γ ⊢< j > app i j A B t u : B <[ u .. ]

(* Dependent pairs *)
(* Only for relevant types, because we already have all inductive types in Prop
  using the impredicative encoding. Moreover, sigmas with mixed relevance can be
  constructed by boxing irrelevant types *)

| type_sigma :
    ∀ Γ n m A B,
      Γ ⊢< Ax (ty n) > A : Sort (ty n) →
      Γ ,, (ty n , A) ⊢< Ax (ty m) > B : Sort (ty m) →
      Γ ⊢< Ax (ty (max n m)) > Sigma (ty n) (ty m) A B : Sort (ty (max n m))

| type_pair :
    ∀ Γ n m A B a b,
      Γ ⊢< Ax (ty n) > A : Sort (ty n) →
      Γ ,, (ty n , A) ⊢< Ax (ty m) > B : Sort (ty m) →
      Γ ⊢< ty n > a : A →
      Γ ⊢< ty m > b : B <[a..] →
      Γ ⊢< ty (max n m) > pair (ty n) (ty m) A B a b : Sigma (ty n) (ty m) A B

| type_pi1 :
    ∀ Γ n m A B t,
      Γ ⊢< Ax (ty n) > A : Sort (ty n) →
      Γ ,, (ty n , A) ⊢< Ax (ty m) > B : Sort (ty m) →
      Γ ⊢< ty (max n m) > t : Sigma (ty n) (ty m) A B →
      Γ ⊢< ty n > pi1 (ty n) (ty m) A B t : A

| type_pi2 :
    ∀ Γ n m A B t,
      Γ ⊢< Ax (ty n) > A : Sort (ty n) →
      Γ ,, (ty n , A) ⊢< Ax (ty m) > B : Sort (ty m) →
      Γ ⊢< ty (max n m) > t : Sigma (ty n) (ty m) A B →
      Γ ⊢< ty m > pi2 (ty n) (ty m) A B t : B <[(pi1 (ty n) (ty m) A B t)..]

(* Natural numbers *)

| type_nat :
    ∀ Γ,
      ⊢ Γ →
      Γ ⊢< ty 1 > Nat : Sort (ty 0)

| type_zero :
    ∀ Γ,
      ⊢ Γ →
      Γ ⊢< ty 0 > zero : Nat

| type_succ :
    ∀ Γ t,
      Γ ⊢< ty 0 > t : Nat ->
      Γ ⊢< ty 0 > succ t : Nat

| type_rec :
    ∀ Γ l P p_zero p_succ t,
      Γ ,, (ty 0 , Nat) ⊢< Ax l > P : Sort l ->
      Γ ⊢< l > p_zero : P <[ zero .. ] ->
      Γ ,, (ty 0 , Nat) ,, (l , P) ⊢< l > p_succ : P <[ (succ (var 1)) .: (shift >> (shift >> var)) ] ->
      Γ ⊢< ty 0 > t : Nat ->
      Γ ⊢< l > rec l P p_zero p_succ t : P <[ t .. ]

(* Equality *)

| type_Eq :
    ∀ Γ l A a b,
      Γ ⊢< Ax l > A : Sort l ->
      Γ ⊢< l > a : A ->
      Γ ⊢< l > b : A ->
      Γ ⊢< Ax prop > Eq l A a b : Sort prop

| type_J :
    ∀ Γ l i A a P p b e,
      Γ ⊢< Ax l > A : Sort l ->
      Γ ⊢< l > a : A ->
      Γ ,, (l , A) ⊢< Ax i > P : Sort i ->
      Γ ⊢< i > p : P <[a..] ->
      Γ ⊢< l > b : A ->
      Γ ⊢< prop > e : Eq l A a b ->
      Γ ⊢< i > J l i A a P p b e : P <[b..]

(* Cumulativity using a one-field record with beta/eta, so that Lift l A is
  in definitional isomorphism with A. This is the approach taken in the Agda stdlib:
  https://github.com/agda/agda-stdlib/blob/master/src/Level.agda
  Note that, for l = prop, we get a boxing operation for irrelevant types. *)

| type_Lift :
    ∀ Γ l A,
      Γ ⊢< Ax l > A : Sort l ->
      Γ ⊢< Ax (Ax l) > Lift l A : Sort (Ax l)

| type_lift :
    ∀ Γ l A a,
      Γ ⊢< Ax l > A : Sort l ->
      Γ ⊢< l > a : A ->
      Γ ⊢< Ax l > lift l A a : Lift l A

| type_lower :
    ∀ Γ l A t,
      Γ ⊢< Ax l > A : Sort l ->
      Γ ⊢< Ax l > t : Lift l A ->
      Γ ⊢< l > lower l A t : A

(* | type_obseq :
    ∀ Γ n A a b,
    Γ ⊢< Ax (ty n) > A : Sort (ty n) ->
    Γ ⊢< ty n > a : A ->
    Γ ⊢< ty n > b : A ->
    Γ ⊢< Ax prop > obseq (ty n) A a b : Sort prop *)

(* | type_obsrefl :
    ∀ Γ n A a,
      Γ ⊢< Ax (ty n) > A : Sort (ty n) ->
      Γ ⊢< ty n > a : A ->
      Γ ⊢< prop > obsrefl (ty n) A a : obseq (ty n) A a a *)

| type_cast :
    ∀ Γ i A B e a,
    Γ ⊢< Ax i > A : Sort i ->
    Γ ⊢< Ax i > B : Sort i ->
    Γ ⊢< prop > e : Eq (Ax i) (Sort i) A B ->
    Γ ⊢< i > a : A ->
    Γ ⊢< i > cast i A B e a : B

| type_injpi1 :
  ∀ Γ i n A1 A2 B1 B2 e,
    Γ ⊢< Ax i > A1 : Sort i ->
    Γ ,, (i, A1) ⊢< Ax (ty n) > B1 : Sort (ty n) ->
    Γ ⊢< Ax i > A2 : Sort i ->
    Γ ,, (i, A2) ⊢< Ax (ty n) > B2 : Sort (ty n) ->
    Γ ⊢< prop > e : Eq (Ax (Ru i (ty n))) (Sort (Ru i (ty n))) (Pi i (ty n) A1 B1) (Pi i (ty n) A2 B2) ->
    Γ ⊢< prop > injpi1 i (ty n) A1 A2 B1 B2 e : Eq (Ax i) (Sort i) A2 A1

| type_injpi2 :
  ∀ Γ i n A1 A2 B1 B2 e a2,
    Γ ⊢< Ax i > A1 : Sort i ->
    Γ ,, (i, A1) ⊢< Ax (ty n) > B1 : Sort (ty n) ->
    Γ ⊢< Ax i > A2 : Sort i ->
    Γ ,, (i, A2) ⊢< Ax (ty n) > B2 : Sort (ty n) ->
    Γ ⊢< prop > e : Eq (Ax (Ru i (ty n))) (Sort (Ru i (ty n))) (Pi i (ty n) A1 B1) (Pi i (ty n) A2 B2) ->
    Γ ⊢< i > a2 : A2 ->
    let a1 := cast i A2 A1 (injpi1 i (ty n) A1 A2 B1 B2 e) a2 in
    Γ ⊢< prop > injpi2 i (ty n) A1 A2 B1 B2 e a2 : Eq (Ax (ty n)) (Sort (ty n)) (B1<[a1..]) (B2 <[a2..])

| type_sum Γ i j A B :
    Γ ⊢< Ax (ty i) > A : Sort (ty i) →
    Γ ⊢< Ax (ty j) > B : Sort (ty j) →
    Γ ⊢< Ax (ty (max i j)) > tysum (ty i) (ty j) A B : Sort (ty (max i j))

| type_inl Γ i j A B a :
    Γ ⊢< Ax (ty i) > A : Sort (ty i) →
    Γ ⊢< Ax (ty j) > B : Sort (ty j) →
    Γ ⊢< ty i > a : A →
    Γ ⊢< ty (max i j) > inl (ty i) (ty j) A B a : tysum (ty i) (ty j) A B

| type_inr Γ i j A B b :
    Γ ⊢< Ax (ty i) > A : Sort (ty i) →
    Γ ⊢< Ax (ty j) > B : Sort (ty j) →
    Γ ⊢< ty j > b : B →
    Γ ⊢< ty (max i j) > inr (ty i) (ty j) A B b : tysum (ty i) (ty j) A B

| type_sum_rec Γ i j l A B P pl pr t :
    Γ ⊢< Ax (ty i) > A : Sort (ty i) →
    Γ ⊢< Ax (ty j) > B : Sort (ty j) →
    Γ ,, (ty (max i j), tysum (ty i) (ty j) A B) ⊢< Ax (ty j) > P : Sort l →
    Γ ,, (ty i, A) ⊢< l > pl : P <[ (inl (ty i) (ty j) (S ⋅ A) (S ⋅ B) (var 0)) .: S >> var ] →
    Γ ,, (ty j, B) ⊢< l > pr : P <[ (inr (ty i) (ty j) (S ⋅ A) (S ⋅ B) (var 0)) .: S >> var ] →
    Γ ⊢< ty (max i j) > t : tysum (ty i) (ty j) A B →
    Γ ⊢< l > sum_rec (ty i) (ty j) l A B P pl pr t : P <[ t .. ]

| type_conv :
    ∀ Γ l A B t,
      Γ ⊢< l > t : A ->
      Γ ⊢< Ax l > A ≡ B : Sort l ->
      Γ ⊢< l > t : B

with conversion : ctx -> level -> term -> term -> term -> Prop :=


| conv_var :
    ∀ Γ x l A,
      ⊢ Γ →
      Γ ∋< l > x : A →
      Γ ⊢< l > var x ≡ var x : A

| conv_sort :
    ∀ Γ l,
      ⊢ Γ →
      Γ ⊢< Ax (Ax l) > Sort l ≡ Sort l : Sort (Ax l)

| conv_pi :
    ∀ Γ i j A B A' B',
      Γ ⊢< Ax i > A : Sort i →
      Γ ⊢< Ax i > A ≡ A' : Sort i →
      Γ ,, (i , A) ⊢< Ax j > B ≡ B' : Sort j →
      Γ ⊢< Ax (Ru i j) > Pi i j A B ≡ Pi i j A' B' : Sort (Ru i j)

| conv_lam :
    ∀ Γ i j A B t A' B' t',
      Γ ⊢< Ax i > A : Sort i →
      Γ ⊢< Ax i > A ≡ A' : Sort i →
      Γ ,, (i , A) ⊢< Ax j > B ≡ B': Sort j →
      Γ ,, (i , A) ⊢< j > t ≡ t' : B →
      Γ ⊢< Ru i j > lam i j A B t ≡ lam i j A' B' t' : Pi i j A B

| conv_app :
    ∀ Γ i j A B t u A' B' t' u',
      Γ ⊢< Ax i > A : Sort i →
      Γ ⊢< Ax i > A ≡ A' : Sort i →
      Γ ,, (i , A) ⊢< Ax j > B ≡ B': Sort j →
      Γ ⊢< Ru i j > t ≡ t' : Pi i j A B →
      Γ ⊢< i > u ≡ u' : A →
      Γ ⊢< j > app i j A B t u ≡ app i j A' B' t' u' : B <[ u .. ]

| conv_sigma :
    ∀ Γ n m A B A' B',
      Γ ⊢< Ax (ty n) > A : Sort (ty n) →
      Γ ⊢< Ax (ty n) > A ≡ A' : Sort (ty n) →
      Γ ,, (ty n , A) ⊢< Ax (ty m) > B ≡ B' : Sort (ty m) →
      Γ ⊢< Ax (ty (max n m)) > Sigma (ty n) (ty m) A B ≡ Sigma (ty n) (ty m) A' B' : Sort (ty (max n m))

| conv_pair :
    ∀ Γ n m A B a b A' B' a' b',
      Γ ⊢< Ax (ty n) > A : Sort (ty n) →
      Γ ⊢< Ax (ty n) > A ≡ A' : Sort (ty n) →
      Γ ,, (ty n , A) ⊢< Ax (ty m) > B ≡ B' : Sort (ty m) →
      Γ ⊢< ty n > a ≡ a' : A →
      Γ ⊢< ty m > b ≡ b' : B <[a..] →
      Γ ⊢< ty (max n m) > pair (ty n) (ty m) A B a b ≡ pair (ty n) (ty m) A' B' a' b' : Sigma (ty n) (ty m) A B

| conv_pi1 :
    ∀ Γ n m A B t A' B' t',
      Γ ⊢< Ax (ty n) > A : Sort (ty n) →
      Γ ⊢< Ax (ty n) > A ≡ A' : Sort (ty n) →
      Γ ,, (ty n , A) ⊢< Ax (ty m) > B ≡ B' : Sort (ty m) →
      Γ ⊢< ty (max n m) > t ≡ t' : Sigma (ty n) (ty m) A B →
      Γ ⊢< ty n > pi1 (ty n) (ty m) A B t ≡ pi1 (ty n) (ty m) A' B' t' : A

| conv_pi2 :
    ∀ Γ n m A B t A' B' t',
      Γ ⊢< Ax (ty n) > A : Sort (ty n) →
      Γ ⊢< Ax (ty n) > A ≡ A' : Sort (ty n) →
      Γ ,, (ty n , A) ⊢< Ax (ty m) > B ≡ B' : Sort (ty m) →
      Γ ⊢< ty (max n m) > t ≡ t' : Sigma (ty n) (ty m) A B →
      Γ ⊢< ty m > pi2 (ty n) (ty m) A B t ≡ pi2 (ty n) (ty m) A' B' t' : B <[(pi1 (ty n) (ty m) A B t)..]

| conv_nat :
    ∀ Γ,
      ⊢ Γ →
      Γ ⊢< ty 1 > Nat ≡ Nat : Sort (ty 0)

| conv_zero :
    ∀ Γ,
      ⊢ Γ →
      Γ ⊢< ty 0 > zero ≡ zero : Nat

| conv_succ :
    ∀ Γ t t',
      Γ ⊢< ty 0 > t ≡ t' : Nat ->
      Γ ⊢< ty 0 > succ t ≡ succ t' : Nat

| conv_rec :
    ∀ Γ l P p_zero p_succ t P' p_zero' p_succ' t',
      Γ ,, (ty 0 , Nat) ⊢< Ax l > P : Sort l ->
      Γ ,, (ty 0 , Nat) ⊢< Ax l > P ≡ P' : Sort l ->
      Γ ⊢< l > p_zero ≡ p_zero' : P <[ zero .. ] ->
      Γ ,, (ty 0 , Nat) ,, (l , P) ⊢< l > p_succ ≡ p_succ' : P <[ (succ (var 1)) .: (shift >> (shift >> var)) ] ->
      Γ ⊢< ty 0 > t ≡ t' : Nat ->
      Γ ⊢< l > rec l P p_zero p_succ t ≡ rec l P' p_zero' p_succ' t' : P <[ t .. ]

| conv_Eq :
    ∀ Γ l A A' a a' b b',
      Γ ⊢< Ax l > A ≡ A' : Sort l ->
      Γ ⊢< l > a ≡ a' : A ->
      Γ ⊢< l > b ≡ b' : A ->
      Γ ⊢< Ax prop > Eq l A a b ≡ Eq l A' a' b' : Sort prop

| conv_J :
    ∀ Γ l i A A' a a' P P' p p' b b' e e',
      Γ ⊢< Ax l > A : Sort l ->
      Γ ⊢< Ax l > A ≡ A' : Sort l ->
      Γ ⊢< l > a ≡ a' : A ->
      Γ ,, (l , A) ⊢< Ax i > P ≡ P' : Sort i ->
      Γ ⊢< i > p ≡ p' : P <[a..] ->
      Γ ⊢< l > b ≡ b' : A ->
      Γ ⊢< prop > e ≡ e' : Eq l A a b ->
      Γ ⊢< i > J l i A a P p b e ≡ J l i A' a' P' p' b' e' : P <[b..]

| conv_Lift :
    ∀ Γ l A A',
      Γ ⊢< Ax l > A ≡ A' : Sort l ->
      Γ ⊢< Ax (Ax l) > Lift l A ≡ Lift l A' : Sort (Ax l)

| conv_lift :
    ∀ Γ l A A' a a',
      Γ ⊢< Ax l > A ≡ A' : Sort l ->
      Γ ⊢< l > a ≡ a' : A ->
      Γ ⊢< Ax l > lift l A a ≡ lift l A' a' : Lift l A

| conv_lower :
    ∀ Γ l A A' a a',
      Γ ⊢< Ax l > A ≡ A' : Sort l ->
      Γ ⊢< Ax l > a ≡ a' : Lift l A ->
      Γ ⊢< l > lower l A a ≡ lower l A' a' : A


| conv_cast :
  ∀ Γ i A A' B B' e e' a a',
    Γ ⊢< Ax i > A ≡ A' : Sort i ->
    Γ ⊢< Ax i > B ≡ B' : Sort i ->
    Γ ⊢< prop > e ≡ e' : Eq (Ax i) (Sort i) A B ->
    Γ ⊢< i > a ≡ a' : A ->
    Γ ⊢< i > cast i A B e a ≡ cast i A' B' e' a' : B

| conv_injpi1 :
  ∀ Γ i n A1 A1' A2 A2' B1 B1' B2 B2' e e',
    Γ ⊢< Ax i > A1 : Sort i ->
    Γ ⊢< Ax i > A1 ≡ A1' : Sort i ->
    Γ ,, (i, A1) ⊢< Ax (ty n) > B1 ≡ B1' : Sort (ty n) ->
    Γ ⊢< Ax i > A2 : Sort i ->
    Γ ⊢< Ax i > A2 ≡ A2' : Sort i ->
    Γ ,, (i, A2) ⊢< Ax (ty n) > B2 ≡ B2' : Sort (ty n) ->
    Γ ⊢< prop > e ≡ e' : Eq (Ax (Ru i (ty n))) (Sort (Ru i (ty n))) (Pi i (ty n) A1 B1) (Pi i (ty n) A2 B2) ->
    Γ ⊢< prop > injpi1 i (ty n) A1 A2 B1 B2 e ≡ injpi1 i (ty n) A1' A2' B1' B2' e' : Eq (Ax i) (Sort i) A2 A1

| conv_injpi2 :
  ∀ Γ i n A1 A1' A2 A2' B1 B1' B2 B2' e e' a2 a2',
    Γ ⊢< Ax i > A1 : Sort i ->
    Γ ⊢< Ax i > A1 ≡ A1' : Sort i ->
    Γ ,, (i, A1) ⊢< Ax (ty n) > B1 ≡ B1' : Sort (ty n) ->
    Γ ⊢< Ax i > A2 : Sort i ->
    Γ ⊢< Ax i > A2 ≡ A2' : Sort i ->
    Γ ,, (i, A2) ⊢< Ax (ty n) > B2 ≡ B2' : Sort (ty n) ->
    Γ ⊢< prop > e ≡ e' : Eq (Ax (Ru i (ty n))) (Sort (Ru i (ty n))) (Pi i (ty n) A1 B1) (Pi i (ty n) A2 B2) ->
    Γ ⊢< i > a2 ≡ a2' : A2 ->
    let a1 := cast i A2 A1 (injpi1 i (ty n) A1 A2 B1 B2 e) a2 in
    Γ ⊢< prop > injpi2 i (ty n) A1 A2 B1 B2 e a2 ≡ injpi2 i (ty n) A1' A2' B1' B2' e' a2' : Eq (Ax (ty n)) (Sort (ty n)) (B1<[a1..]) (B2 <[a2..])

| conv_sum Γ i j A A' B B' :
    Γ ⊢< Ax (ty i) > A ≡ A' : Sort (ty i) →
    Γ ⊢< Ax (ty j) > B ≡ B' : Sort (ty j) →
    Γ ⊢< Ax (ty (max i j)) > tysum (ty i) (ty j) A B ≡ tysum (ty i) (ty j) A' B' : Sort (ty (max i j))

| conv_inl Γ i j A A' B B' a a' :
    Γ ⊢< Ax (ty i) > A ≡ A' : Sort (ty i) →
    Γ ⊢< Ax (ty j) > B ≡ B' : Sort (ty j) →
    Γ ⊢< ty i > a ≡ a' : A →
    Γ ⊢< ty (max i j) > inl (ty i) (ty j) A B a ≡ inl (ty i) (ty j) A' B' a' : tysum (ty i) (ty j) A B

| conv_inr Γ i j A A' B B' b b' :
    Γ ⊢< Ax (ty i) > A ≡ A' : Sort (ty i) →
    Γ ⊢< Ax (ty j) > B ≡ B' : Sort (ty j) →
    Γ ⊢< ty j > b ≡ b' : B →
    Γ ⊢< ty (max i j) > inr (ty i) (ty j) A B b ≡ inr (ty i) (ty j) A' B' b' : tysum (ty i) (ty j) A B

| conv_sum_rec Γ i j l A A' B B' P P' pl pl' pr pr' t t' :
    Γ ⊢< Ax (ty i) > A ≡ A' : Sort (ty i) →
    Γ ⊢< Ax (ty j) > B ≡ B' : Sort (ty j) →
    Γ ,, (ty (max i j), tysum (ty i) (ty j) A B) ⊢< Ax (ty j) > P ≡ P' : Sort l →
    Γ ,, (ty i, A) ⊢< l > pl ≡ pl' : P <[ (inl (ty i) (ty j) (S ⋅ A) (S ⋅ B) (var 0)) .: S >> var ] →
    Γ ,, (ty j, B) ⊢< l > pr ≡ pr' : P <[ (inr (ty i) (ty j) (S ⋅ A) (S ⋅ B) (var 0)) .: S >> var ] →
    Γ ⊢< ty (max i j) > t ≡ t' : tysum (ty i) (ty j) A B →
    Γ ⊢< l > sum_rec (ty i) (ty j) l A B P pl pr t ≡ sum_rec (ty i) (ty j) l A' B' P' pl' pr' t' : P <[ t .. ]

| conv_conv :
    ∀ Γ l A B t t',
      Γ ⊢< l > t ≡ t' : A ->
      Γ ⊢< Ax l > A ≡ B : Sort l ->
      Γ ⊢< l > t ≡ t' : B

| conv_irrel :
    ∀ Γ A t t',
      Γ ⊢< prop > t : A ->
      Γ ⊢< prop > t' : A ->
      Γ ⊢< prop > t ≡ t' : A

| conv_beta :
    ∀ Γ i j A B t u,
      Γ ⊢< Ax i > A : Sort i →
      Γ ,, (i , A) ⊢< Ax j > B : Sort j →
      Γ ,, (i , A) ⊢< j > t : B →
      Γ ⊢< i > u : A →
      Γ ⊢< j > app i j A B (lam i j A B t) u ≡ t <[ u .. ] : B <[ u .. ]


| conv_pi1pair :
    ∀ Γ n m A B a b,
      Γ ⊢< Ax (ty n) > A : Sort (ty n) →
      Γ ,, (ty n , A) ⊢< Ax (ty m) > B : Sort (ty m) →
      Γ ⊢< ty n > a : A →
      Γ ⊢< ty m > b : B <[a..] →
      Γ ⊢< ty n > pi1 (ty n) (ty m) A B (pair (ty n) (ty m) A B a b) ≡ a : A

| conv_pi2pair :
    ∀ Γ n m A B a b,
      Γ ⊢< Ax (ty n) > A : Sort (ty n) →
      Γ ,, (ty n , A) ⊢< Ax (ty m) > B : Sort (ty m) →
      Γ ⊢< ty n > a : A →
      Γ ⊢< ty m > b : B <[a..] →
      Γ ⊢< ty m > pi2 (ty n) (ty m) A B (pair (ty n) (ty m) A B a b) ≡ b : B <[a..]



| conv_rec_zero :
    ∀ Γ l P p_zero p_succ,
      Γ ,, (ty 0 , Nat) ⊢< Ax l > P : Sort l ->
      Γ ⊢< l > p_zero : P <[ zero .. ] ->
      Γ ,, (ty 0 , Nat) ,, (l , P) ⊢< l > p_succ : P <[ (succ (var 1)) .: (shift >> (shift >> var)) ]  ->
      Γ ⊢< l > rec l P p_zero p_succ zero ≡ p_zero : P <[ zero .. ]

| conv_rec_succ :
    ∀ Γ l P p_zero p_succ t,
      Γ ,, (ty 0 , Nat) ⊢< Ax l > P : Sort l ->
      Γ ⊢< l > p_zero : P <[ zero .. ] ->
      Γ ,, (ty 0 , Nat) ,, (l , P) ⊢< l > p_succ : P <[ (succ (var 1)) .: (shift >> (shift >> var)) ]  ->
      Γ ⊢< ty 0 > t : Nat ->
      Γ ⊢< l > rec l P p_zero p_succ (succ t) ≡
          p_succ <[(rec l P p_zero p_succ t) .: t ..] : P <[ (succ t) .. ]

| conv_J_refl :
    ∀ Γ l i A a P p e,
      Γ ⊢< Ax l > A : Sort l ->
      Γ ⊢< l > a : A ->
      Γ ,, (l , A) ⊢< Ax i > P : Sort i ->
      Γ ⊢< i > p : P <[a..] ->
      Γ ⊢< prop > e : Eq l A a a ->
      Γ ⊢< i > J l i A a P p a e ≡ p : P <[a..]




| conv_lower_lift :  (* derivable for l = prop *)
    ∀ Γ n A a,
      Γ ⊢< Ax (ty n) > A : Sort (ty n) ->
      Γ ⊢< ty n > a : A ->
      Γ ⊢< ty n > lower (ty n) A (lift (ty n) A a) ≡ a : A

| conv_lift_lower :  (* ill behaved for l = prop *)
    ∀ Γ n A a,
      Γ ⊢< Ax (ty n) > A : Sort (ty n) ->
      Γ ⊢< Ax (ty n) > a : Lift (ty n) A ->
      Γ ⊢< Ax (ty n) > lift (ty n) A (lower (ty n) A a) ≡ a : Lift (ty n) A

(* | conv_obseq :
  ∀ Γ n A A' a a' b b',
    Γ ⊢< Ax (ty n) > A ≡ A' : Sort (ty n) ->
    Γ ⊢< ty n > a ≡ a' : A ->
    Γ ⊢< ty n > b ≡ b' : A ->
    Γ ⊢< Ax prop > obseq (ty n) A a b ≡ obseq (ty n) A' a' b' : Sort prop *)

(* | conv_obsrefl :
  ∀ n Γ A A' a a',
    Γ ⊢< Ax (ty n) > A ≡ A' : Sort (ty n) ->
    Γ ⊢< ty n > a ≡ a' : A ->
    Γ ⊢< prop > obsrefl (ty n) A a ≡ obsrefl (ty n) A' a' : obseq (ty n) A a a *)


| conv_cast_univ :
    ∀ Γ i e a,
      Γ ⊢< prop > e : Eq (Ax (Ax i)) (Sort (Ax i)) (Sort i) (Sort i) ->
      Γ ⊢< Ax i > a : Sort i ->
      Γ ⊢< Ax i > cast (Ax i) (Sort i) (Sort i) e a ≡ a : Sort i

| conv_cast_nat :
    ∀ Γ e a,
      Γ ⊢< prop > e : Eq (Ax (ty 0)) (Sort (ty 0)) Nat Nat ->
      Γ ⊢< ty 0 > a : Nat ->
      Γ ⊢< ty 0 > cast (ty 0) Nat Nat e a ≡ a : Nat

| conv_cast_pi :
  ∀ Γ i n A1 A2 B1 B2 e f,
    Γ ⊢< Ax i > A1 : Sort i ->
    Γ ,, (i, A1) ⊢< Ax (ty n) > B1 : Sort (ty n) ->
    Γ ⊢< Ax i > A2 : Sort i ->
    Γ ,, (i, A2) ⊢< Ax (ty n) > B2 : Sort (ty n) ->
    Γ ⊢< prop > e : Eq (Ax (Ru i (ty n))) (Sort (Ru i (ty n))) (Pi i (ty n) A1 B1) (Pi i (ty n) A2 B2) ->
    Γ ⊢< Ru i (ty n) > f : Pi i (ty n) A1 B1 ->
    let A1' := S ⋅ A1 in
    let A2' := S ⋅ A2 in
    let B1' := (up_ren S) ⋅ B1 in
    let B2' := (up_ren S) ⋅ B2 in
    let t1 := cast i A2' A1' (injpi1 i (ty n) A1' A2' B1' B2' (S ⋅ e)) (var 0) in
    let t2 := app i (ty n) A1' B1' (S ⋅ f) t1 in
    let t3 := cast (ty n) (B1 <[t1.: S >> var]) B2 (injpi2 i (ty n) A1' A2' B1' B2' (S ⋅ e) (var 0)) t2 in
    let t4 := lam i (ty n) A2 B2 t3 in
    Γ ⊢< Ru i (ty n) > cast (Ru i (ty n)) (Pi i (ty n) A1 B1) (Pi i (ty n) A2 B2) e f ≡ t4 : Pi i (ty n) A2 B2

| conv_sum_rec_inl Γ i j l A B P pl pr a :
    Γ ⊢< Ax (ty i) > A : Sort (ty i) →
    Γ ⊢< Ax (ty j) > B : Sort (ty j) →
    Γ ,, (ty (max i j), tysum (ty i) (ty j) A B) ⊢< Ax (ty j) > P : Sort l →
    Γ ,, (ty i, A) ⊢< l > pl : P <[ (inl (ty i) (ty j) (S ⋅ A) (S ⋅ B) (var 0)) .: S >> var ] →
    Γ ,, (ty j, B) ⊢< l > pr : P <[ (inr (ty i) (ty j) (S ⋅ A) (S ⋅ B) (var 0)) .: S >> var ] →
    Γ ⊢< ty i > a : A →
    Γ ⊢< l > sum_rec (ty i) (ty j) l A B P pl pr (inl (ty i) (ty j) A B a) ≡ pl <[ a .. ] : P <[ (inl (ty i) (ty j) A B a) .. ]

| conv_sum_rec_inr Γ i j l A B P pl pr b :
    Γ ⊢< Ax (ty i) > A : Sort (ty i) →
    Γ ⊢< Ax (ty j) > B : Sort (ty j) →
    Γ ,, (ty (max i j), tysum (ty i) (ty j) A B) ⊢< Ax (ty j) > P : Sort l →
    Γ ,, (ty i, A) ⊢< l > pl : P <[ (inl (ty i) (ty j) (S ⋅ A) (S ⋅ B) (var 0)) .: S >> var ] →
    Γ ,, (ty j, B) ⊢< l > pr : P <[ (inr (ty i) (ty j) (S ⋅ A) (S ⋅ B) (var 0)) .: S >> var ] →
    Γ ⊢< ty j > b : B →
    Γ ⊢< l > sum_rec (ty i) (ty j) l A B P pl pr (inr (ty i) (ty j) A B b) ≡ pr <[ b .. ] : P <[ (inr (ty i) (ty j) A B b) .. ]

| conv_sym :
    ∀ Γ l t u A,
      Γ ⊢< l > t ≡ u : A ->
      Γ ⊢< l > u ≡ t : A

| conv_trans :
    ∀ Γ l t u v A,
      Γ ⊢< l > t ≡ u : A ->
      Γ ⊢< l > u ≡ v : A ->
      Γ ⊢< l > t ≡ v : A

with ctx_typing : ctx -> Prop :=
| ctx_nil :
    ⊢ ∙

| ctx_cons :
    ∀ Γ l A,
      ⊢ Γ →
      Γ ⊢< Ax l > A : Sort l →
      ⊢ Γ ,, (l , A)

where "Γ ⊢< l > t : A" := (typing Γ l t A)
and   "Γ ⊢< l > t ≡ u : A" := (conversion Γ l t u A)
and   "⊢ Γ" := (ctx_typing Γ).


Reserved Notation "Γ ⊢r ρ : Δ" (at level 50, ρ, Δ at next level).

Inductive WellRen (Γ : ctx) (ρ : nat → nat) : ctx → Prop :=
| well_rempty : Γ ⊢r ρ : ∙
| well_rcons Δ l A :
  Γ ⊢r (↑ >> ρ) : Δ →
  Γ ∋< l > ρ 0 : (S >> ρ) ⋅ A →
  Γ ⊢r ρ : Δ ,, (l , A)
where "Γ ⊢r ρ : Δ" := (WellRen Γ ρ Δ).


Reserved Notation "Γ ⊢s σ : Δ" (at level 50, σ, Δ at next level).

Reserved Notation "Γ ⊢s σ ≡ τ : Δ" (at level 50, σ, τ, Δ at next level).

Inductive WellSubst (Γ : ctx) : ctx -> (nat -> term) -> Prop :=
| well_sempty (σ : nat -> term) :
  Γ ⊢s σ : ∙
| well_scons (σ : nat -> term) (Δ : ctx) l (A : term) :
  Γ ⊢s (↑ >> σ) : Δ ->
  Γ ⊢< l > σ 0 : A <[↑ >> σ] ->
  Γ ⊢s σ : (Δ ,, (l , A))
where "Γ ⊢s σ : Δ" := (WellSubst Γ Δ σ).

Inductive ConvSubst (Γ : ctx) : ctx -> (nat -> term) -> (nat -> term) -> Prop :=
| conv_sempty (σ τ : nat -> term) : Γ ⊢s σ ≡ τ : ∙
| conv_scons (σ τ : nat -> term) (Δ : ctx) l A :
  Γ ⊢s (↑ >> σ) ≡ (↑ >> τ) : Δ ->
  Γ ⊢< l > σ var_zero ≡ τ var_zero: A <[↑ >> σ] ->
  Γ ⊢s σ ≡ τ : Δ ,, (l , A)
where "Γ ⊢s σ ≡ τ : Δ" := (ConvSubst Γ Δ σ τ).

Reserved Notation "⊢ Γ ≡ Δ" (at level 50, Δ at next level).

Inductive ConvCtx : ctx -> ctx -> Prop :=
| conv_cempty : ⊢ ∙ ≡ ∙
| conv_ccons Γ A Δ B l :
  ⊢ Γ ≡ Δ ->
  Γ ⊢< Ax l > A ≡ B : Sort l ->
  ⊢ (Γ ,, ( l , A)) ≡ (Δ ,, (l , B))
where "⊢ Γ ≡ Δ" := (ConvCtx Γ Δ).
