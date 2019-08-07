(** Type syntax:*)

Inductive Ty: Set :=
  | Unit : Ty
  | Arr  : Ty -> Ty -> Ty
  | Ref : Ty -> Ty
.

Notation "A ⇒  B" := (Arr A B) (at level 17, right associativity).
