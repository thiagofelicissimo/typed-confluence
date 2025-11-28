
(* This file shows why we only need to consider a non-dependent J in the def of the system:
    the dependent version of J is derivable from it in the presence of proof irrelevance *)


Axiom Eq : forall (A : Type), A -> A -> SProp.

Axiom refl : forall A a, Eq A a a.


Definition sigma_prop (A : SProp) (B : A -> SProp) : SProp := forall P, (forall x:A, B x -> P) -> P.

Definition fst_prop {A B}: sigma_prop A B -> A := fun f => f A (fun a b => a).

Definition snd_prop {A B}: forall x : sigma_prop A B, B (fst_prop x) := fun f => f (B (fst_prop f)) (fun a b => b).

Definition mk_sigma_prop {A B} : forall x : A, B x -> sigma_prop A B := fun a b P f => f a b.


Axiom J_sprop : forall (A : Type) (a : A) (P : A -> SProp) (p : P a) (b : A) (e : Eq A a b), P b.

Lemma DepJ_sprop (A : Type) (a : A) (P : forall y, Eq A a y -> SProp) (p : P a (refl A a)) (b : A) (e : Eq A a b) : P b e.
Proof.
    unshelve eapply (@snd_prop (Eq A a b) (fun e => P b e) _).
    eapply (J_sprop _ _ (fun b => sigma_prop (Eq A a b) (fun e0 : Eq A a b => P b e0))); eauto.
    eapply mk_sigma_prop; eauto.
Qed.
    
Axiom J_type : forall (A : Type) (a : A) (P : A -> Type) (p : P a) (b : A) (e : Eq A a b), P b.

Inductive Sigma (A : SProp) (B : A -> Type) : Type := 
    | mk_sigma : forall x : A, B x -> Sigma A B.

Definition proj1 {A} {B} : Sigma A B -> A := fun x => match x with | mk_sigma _ _ x _ => x end.

Definition proj2 {A} {B} : forall x : Sigma A B, B (proj1 x) := fun x => match x with | mk_sigma _ _ _ x => x end.

Lemma DepJ_type (A : Type) (a : A) (P : forall y, Eq A a y -> Type) (p : P a (refl A a)) (b : A) (e : Eq A a b) : P b e.
Proof.
    unshelve eapply (@proj2 (Eq A a b) (fun e => P b e) _).
    eapply (J_type  _ _ (fun b => Sigma (Eq A a b) (fun e0 : Eq A a b => P b e0))); eauto.
    econstructor. eauto.
Qed.
