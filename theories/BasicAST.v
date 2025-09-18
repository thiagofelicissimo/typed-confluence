From Stdlib Require Import Utf8 String.

Set Primitive Projections.

(** Universe level *)
Inductive level := 
| ty (n : nat) | prop.
