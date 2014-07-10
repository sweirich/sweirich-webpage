(** We define here the tags for the two sorts of Fsub terms.  This
    datatype is shared across all the developments and adequacy
    proofs, saving us the trouble of having to translate between
    different, isomorphic tag datatypes all the time. *)

Require Import Metatheory.

Inductive tag : Set :=
  | Typ : tag
  | Exp : tag.

Theorem eq_tag_dec : forall x y : tag, {x = y} + {x <> y}.
Proof.
  decide equality.
Qed.
