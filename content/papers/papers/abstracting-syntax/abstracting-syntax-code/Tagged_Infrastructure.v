(** Infrastructure lemmas and tactic definitions for Fsub. *)

Require Export Tagged_Definitions.
Set Printing Implicit.


(* ********************************************************************** *)
(** * #<a name="pick_fresh"></a># The "[pick fresh]" tactic *)

Ltac gather_atoms :=
  let A := gather_atoms_with (fun x : atoms => x) in
  let B := gather_atoms_with (fun x : atom => singleton x) in
  let C := gather_atoms_with (fun x : exp => fv_te x) in
  let D := gather_atoms_with (fun x : exp => fv_ee x) in
  let E := gather_atoms_with (fun x : typ => fv_tt x) in
  let F := gather_atoms_with (fun x : env => dom x) in
  let G := gather_atoms_with (fun x : senv => dom x) in
  constr:(A `union` B `union` C `union` D `union` E `union` F `union` G).

Tactic Notation "pick" "fresh" ident(x) :=
  let L := gather_atoms in (pick fresh x for L).

Tactic Notation
      "pick" "fresh" ident(atom_name) "and" "apply" constr(lemma) :=
  let L := gather_atoms in
  pick fresh atom_name excluding L and apply lemma.


(* ********************************************************************** *)
(** * #<a name="properties"></a># Properties of opening and substitution *)

Lemma open_rec_lc_aux :
  forall A B C (T : syntax A) j (V : syntax B) i (U : syntax C),
  i <> j ->
  open_rec j V T = open_rec i U (open_rec j V T) ->
  T = open_rec i U T.
Proof with eauto*.
  induction T; intros j V i U Neq H; simpl in *; inversion H; f_equal...
  Case "bvar".
    destruct (j === n)... destruct (i === n)...
Qed.

Lemma open_rec_lc : forall A B (T : syntax A) (U : syntax B) k,
  lc T ->
  T = open_rec k U T.
Proof with auto*.
  intros A B T U k Hlc. revert k.
  induction Hlc; intros k; simpl; f_equal; auto*;
  try solve [
    unfold open in *;
    pick fresh x;
    solve [
      apply open_rec_lc_aux with (j := 0) (V := @fvar Exp x); auto*
    | apply open_rec_lc_aux with (j := 0) (V := @fvar Typ x); auto*
    ]
  ].
Qed.

Lemma subst_fresh : forall A B (Z : atom) (U : syntax A) (T : syntax B),
   Z `notin` fv T ->
   T = subst Z U T.
Proof with auto*.
  induction T; simpl; intro H; f_equal...
  Case "fvar".
    destruct (a == Z)...
    absurd_hyp H; fsetdec.
Qed.

Lemma subst_open_rec :
  forall A B C (T1 : syntax A) (T2 : syntax B) (X : atom) (P : syntax C) k,
  lc P ->
  subst X P (open_rec k T2 T1) = open_rec k (subst X P T2) (subst X P T1).
Proof with auto*.
  intros A B C T1 T2 X P k WP. revert k.
  induction T1; intros k; simpl; f_equal...
  Case "bvar".
    destruct (k === n); subst...
    destruct B; destruct T...
  Case "fvar".
    destruct (a == X); subst...
    apply open_rec_lc...
    destruct C; destruct T; simpl...
Qed.

Lemma subst_open :
  forall A B C (T1 : syntax A) (T2 : syntax B) (X : atom) (P : syntax C),
  lc P ->
  subst X P (open T1 T2) = open (subst X P T1) (subst X P T2).
Proof with auto*.
  intros.
  unfold open.
  apply subst_open_rec...
Qed.

Lemma subst_open_var : forall A B C (X Y : atom) (P : syntax A) (T : syntax B),
  Y <> X ->
  lc P ->
  open (subst X P T) (@fvar C Y) = subst X P (open T (@fvar C Y)).
Proof with auto*.
  intros A B C X Y P T Neq Wu.
  unfold open.
  rewrite subst_open_rec...
  simpl.
  destruct (Y == X)...
Qed.

Lemma subst_intro_rec : forall A B (X : atom) (T2 : syntax A) (U : syntax B) k,
  X `notin` fv T2 ->
  open_rec k U T2 = subst X U (open_rec k (@fvar B X) T2).
Proof with auto*.
  induction T2; intros U k Fr; simpl in *; f_equal...
  Case "bvar".
    destruct (k === n)... simpl.
    destruct B; destruct T; simpl; auto; destruct (X == X)...
  Case "fvar".
    destruct (a == X)... absurd_hyp Fr; fsetdec.
Qed.

Lemma subst_intro : forall A B (X : atom) (T2 : syntax A) (U : syntax B),
  X `notin` fv T2 ->
  open T2 U = subst X U (open T2 (@fvar B X)).
Proof with auto*.
  intros.
  unfold open.
  apply subst_intro_rec...
Qed.

Notation subst_tt_open_tt := subst_open (only parsing).

Notation subst_tt_open_tt_var := subst_open_var (only parsing).
Notation subst_te_open_te_var := subst_open_var (only parsing).
Notation subst_te_open_ee_var := subst_open_var (only parsing).
Notation subst_ee_open_te_var := subst_open_var (only parsing).
Notation subst_ee_open_ee_var := subst_open_var (only parsing).

Notation subst_tt_intro := subst_intro (only parsing).
Notation subst_te_intro := subst_intro (only parsing).
Notation subst_ee_intro := subst_intro (only parsing).

Notation subst_tt_fresh := subst_fresh (only parsing).
Notation subst_te_fresh := subst_fresh (only parsing).
Notation subst_ee_fresh := subst_fresh (only parsing).


(* *********************************************************************** *)
(** * #<a name="lc"></a># Local closure is preserved under substitution *)

Lemma subst_lc : forall A B (Z : atom) (P : syntax A) (T : syntax B),
  lc T ->
  lc P ->
  lc (subst Z P T).
Proof with auto*.
  intros A B Z P T HT HP.
  induction HT; simpl; auto*;
  try solve [
    econstructor;
    try instantiate (1 := L `union` singleton Z);
    intros;
    try rewrite subst_open_var;
    auto
  ].
  Case "fvar".
    destruct (X == Z)...
    destruct A; destruct A0; simpl...
Qed.


(* *********************************************************************** *)
(** * #<a name="auto"></a># Automation *)

Hint Resolve subst_lc.

Hint Extern 1 (binds _ (?F (subst_tt ?X ?U ?T)) _) =>
  unsimpl (subst_tb X U (F T)).

Hint Extern 1 (binds _ Typ _) =>
  match goal with
    | H : binds _ (bind_sub ?U) _ |- _ =>
      change Typ with (to_tag (bind_sub U))
  end.

Hint Extern 1 (binds _ Exp _) =>
  match goal with
    | H : binds _ (bind_typ ?U) _ |- _ =>
      change Exp with (to_tag (bind_typ U))
  end.
