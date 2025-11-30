(* This file shows that the usual optimization of checking if two non-annotated terms are syntaxically equal before normalizing them is unsound in the absence of termination. Concretely, we give two terms well-typed with type-in-type which are syntactically equal when forgetting annotations, but which are not convertible. This is obtained by considering Howe's looping combinator derived from the proof of False, and the previously shown fact that it is not a fixpoint combinator *)

Unset Universe Checking.

Axiom A : Type.
Axiom f : A -> A.

Definition Pow X := X -> Type.
Definition Pow2 X := Pow (Pow X).
Definition Neg X := X -> A.

Definition U :=
    forall X, (Pow2 X -> X) -> Pow2 X.

Definition τ := 
    fun t : Pow2 U => 
    fun X : Type => 
    fun g : (Pow2 X -> X) => 
    fun p : Pow X => 
    t (fun x : U => p (g (x X g))).

Definition σ := fun s : U => s U τ.

Definition ρ := fun y : U => τ (σ y).

Definition E x := forall p : Pow U,
    (σ x p) -> p (τ (σ x)).

Definition Q : Pow2 U :=
    fun p => forall x : U, σ x p -> p x.

Definition B : Pow U := fun x => Neg (E x).

Definition C : U := τ Q.

Definition D := forall p, Q p -> p C.

Definition M : Q B :=
    fun x : U => fun k : σ x B =>
    fun l : E x => 
    f (l B k (fun p => l (fun y => p (ρ y)))).

Definition R : D :=
    fun p h => h C (fun x => h (ρ x)).

Definition R' := (fun (p : Pow U) (h : Q (fun y : U => p (ρ y))) => h C (fun x : U => h (ρ x))).

Definition Y : A := R B M R'.

Definition R'' := (fun (p : Pow U) (h : Q (fun y : U => p (ρ (ρ y)))) => h C (fun x : U => h (ρ x))).

Definition M' := (fun (x : U) (k : σ (ρ x) B) (l : E (ρ x)) => f (l B k (fun p : Pow U => l (fun y : U => p (ρ y))))).

Definition Y' : A := R' B M' R''.

(* we can now print R, R', R'' and M, M', erase the annotations 
    and check that we get the same terms *)

Print R.
    (* fun p h => h C (fun x => h (ρ x)) *)
Print R'.
    (* fun p h => h C (fun x => h (ρ x)) *)
Print R''.
    (* fun p h => h C (fun x => h (ρ x)) *)

Print M.
    (* fun x k l => f (l B k (fun p => l (fun y => p (ρ y)))) *)
Print M'.
    (* fun x k l => f (l B k (fun p => l (fun y => p (ρ y)))) *)

(* As shown by coquand and bathe, we cannot have Y \conv f Y. The following proof shows Y \conv f Y', and thus we cannot have Y \conv Y' *)

Definition M_ := (fun (x : U) (k : σ x B) (l : E x) => f (l B k (fun p : Pow U => l (fun y : U => p (ρ y))))).

(* we use prop equality, but in the proof everything follows from refl and transitivity, therefore the equality actually holds definitionally *)
Lemma fix_eq : Y = f Y'.
Proof.
    etransitivity. 2:shelve.
    unfold Y.
    unfold M. fold M_.
    unfold R. unfold M_ at 1.
    unfold M_. fold M'. 
    unfold R' at 2. fold R''. 
    reflexivity. Unshelve. fold Y'. reflexivity.
Qed.