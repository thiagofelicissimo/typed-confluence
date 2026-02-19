
(* the following flags are used to control which rules 
  are turned on or off *)
Parameter flag_strongJ : bool.
Parameter flag_obseq : bool.

Definition with_strongJ := flag_strongJ = true.
Definition with_obseq := flag_obseq = true.

(* used for rules that are common to both, like Eq and refl *)
Definition with_strongJ_or_obseq := with_strongJ \/ with_obseq.

Lemma with_inl : with_strongJ -> with_strongJ_or_obseq.
Proof. intro. left. eassumption. Qed.

Lemma with_inr : with_obseq -> with_strongJ_or_obseq.
Proof. intro. right. eassumption. Qed.

Opaque with_strongJ with_obseq.

(* we add these to the hint database, so they are automatically used by auto *)
Hint Resolve with_inl with_inr : core.
