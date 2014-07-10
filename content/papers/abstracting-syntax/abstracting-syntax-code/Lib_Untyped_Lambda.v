Require Import Metatheory.


Module Type CONST.
  Parameter const : Set.
End CONST.


(* *********************************************************************** *)
(** * Parameterized lambda calculus *)

(** We parameterize the lambda calculus over a set of base constants. *)

Module Lam (Const : CONST).


(* *********************************************************************** *)
(** ** Pre-terms *)

Inductive syntax : Set :=
  | bvar : nat -> syntax
  | fvar : atom -> syntax
  | abs : syntax -> syntax
  | app : syntax -> syntax -> syntax
  | const : Const.const -> syntax.

Coercion bvar : nat >-> syntax.
Coercion fvar : atom >-> syntax.


(* *********************************************************************** *)
(** ** Basic operations *)

Fixpoint open_rec (k : nat) (u : syntax) (e : syntax) {struct e} : syntax :=
  match e with
    | bvar i => if k === i then u else (bvar i)
    | fvar x => fvar x
    | abs e1 => abs (open_rec (S k) u e1)
    | app e1 e2 => app (open_rec k u e1) (open_rec k u e2)
    | const c => const c
  end.

Notation Local "{ k ~> u } t" := (open_rec k u t) (at level 67).

Definition open e u := open_rec 0 u e.

Fixpoint subst (z : atom) (u : syntax) (e : syntax) {struct e} : syntax :=
  match e with
    | bvar i => bvar i
    | fvar x => if x == z then u else (fvar x)
    | abs e1 => abs (subst z u e1)
    | app e1 e2 => app (subst z u e1) (subst z u e2)
    | const c => const c
  end.

Notation Local "[ z ~> u ] e" := (subst z u e) (at level 68).

Fixpoint fv (e : syntax) {struct e} : atoms :=
  match e with
    | bvar i => {}
    | fvar x => singleton x
    | abs e1 => (fv e1)
    | app e1 e2 => (fv e1) `union` (fv e2)
    | const c => {}
  end.

Fixpoint close_rec (k : nat) (x : atom) (e : syntax) {struct e} : syntax :=
  match e with
    | bvar i => bvar i
    | fvar y => if x == y then (bvar k) else (fvar y)
    | abs e1 => abs (close_rec (S k) x e1)
    | app e1 e2 => app (close_rec k x e1) (close_rec k x e2)
    | const c => const c
  end.

Definition close e x := close_rec 0 x e.


(* *********************************************************************** *)
(** ** Local closure *)

Inductive lc : syntax -> Prop :=
  | lc_var : forall x,
      lc (fvar x)
  | lc_abs : forall L e,
      (forall x : atom, x `notin` L -> lc (open e x)) ->
      lc (abs e)
  | lc_app : forall e1 e2,
      lc e1 ->
      lc e2 ->
      lc (app e1 e2)
  | lc_const : forall s,
      lc (const s).

Hint Constructors lc.

Definition body (e : syntax) :=
  exists L, forall x : atom, x `notin` L -> lc (open e x).

Inductive level : nat -> syntax -> Prop :=
  | level_bvar : forall n i,
      i < n ->
      level n (bvar i)
  | level_fvar : forall n x,
      level n (fvar x)
  | level_abs : forall n e,
      level (S n) e ->
      level n (abs e)
  | level_app : forall n e1 e2,
      level n e1 ->
      level n e2 ->
      level n (app e1 e2)
  | level_const : forall n c,
      level n (const c).

Hint Constructors level.


(* *********************************************************************** *)
(** ** Essential properties *)

Lemma open_rec_lc_core : forall e j v i u,
  i <> j ->
  {j ~> v} e = {i ~> u} ({j ~> v} e) ->
  e = {i ~> u} e.
Proof with eauto*.
  induction e; intros j v i u Neq H; simpl in *;
      try solve [inversion H; f_equal; eauto].
  Case "bvar".
    destruct (j === n)...
    destruct (i === n)...
Qed.

Lemma open_rec_lc : forall k u e,
  lc e ->
  e = {k ~> u} e.
Proof with auto.
  intros k u e H.
  generalize dependent k.
  induction H; intros k; simpl; try solve [f_equal; auto].
  Case "abs".
    f_equal...
    pick fresh x for L.
    unfold open in *.
    apply (open_rec_lc_core e 0 x)...
Qed.

Lemma subst_open_rec : forall (x : atom) e1 e2 u k,
  lc u ->
  [x ~> u] ({k ~> e2} e1) = {k ~> [x ~> u] e2} ([x ~> u] e1).
Proof with auto.
  induction e1; intros e2 u k H; simpl in *; f_equal...
  Case "bvar".
    destruct (k === n)...
  Case "fvar".
    destruct (a == x); subst...
    apply open_rec_lc...
Qed.

Lemma subst_open : forall (x : atom) e1 e2 u,
  lc u ->
  [x ~> u] (open e1 e2) = open ([x ~> u] e1) ([x ~> u] e2).
Proof.
  intros.
  unfold open.
  apply subst_open_rec; auto.
Qed.

Lemma subst_open_var : forall (x y : atom) u e,
  y <> x ->
  lc u ->
  open ([x ~> u] e) y = [x ~> u] (open e y).
Proof with auto*.
  intros x y u e Neq H.
  unfold open.
  rewrite subst_open_rec...
  simpl.
  destruct (y == x)...
Qed.

Lemma subst_intro_rec : forall (x : atom) e u k,
  x `notin` fv e ->
  {k ~> u} e = [x ~> u] ({k ~> x} e).
Proof with auto*.
  induction e; intros u k Fr; simpl in *; f_equal...
  Case "bvar".
    destruct (k === n)...
    simpl.
    destruct (x == x)...
  Case "fvar".
    destruct (a == x)...
    absurd_hyp Fr; fsetdec.
Qed.

Lemma subst_intro : forall x e u,
  x `notin` fv e ->
  open e u = subst x u (open e x).
Proof with auto*.
  intros.
  unfold open.
  apply subst_intro_rec...
Qed.

Lemma subst_lc : forall (x : atom) u e,
  lc e ->
  lc u ->
  lc ([x ~> u] e).
Proof with auto.
  intros x u e H J.
  induction H; simpl...
  Case "fvar".
    destruct (x0 == x)...
  Case "abs".
    apply lc_abs with (L := L `union` singleton x).
    intros y Fr.
    rewrite subst_open_var...
Qed.

Lemma subst_fresh : forall (x : atom) u e,
  x `notin` fv e ->
  e = [x ~> u] e.
Proof with auto.
  intros x u e H.
  induction e; simpl in *; f_equal...
  Case "fvar".
    destruct (a == x)...
    absurd_hyp H; fsetdec.
Qed.

Lemma lc_open_from_body : forall e1 e2,
  body e1 ->
  lc e2 ->
  lc (open e1 e2).
Proof.
  intros e1 e2 [L H] J.
  pick fresh x for (L `union` fv e1).
  rewrite (subst_intro x); auto using subst_lc.
Qed.

Lemma lc_open_from_abs : forall e1 e2,
  lc (abs e1) ->
  lc e2 ->
  lc (open e1 e2).
Proof.
  intros e1 e2 H J.
  inversion H; subst.
  pick fresh x for (L `union` fv e1).
  rewrite (subst_intro x); auto using subst_lc.
Qed.

Lemma lc_abs_from_body : forall e,
  body e ->
  lc (abs e).
Proof.
  intros e [L H].
  eauto.
Qed.

Lemma body_from_lc_abs : forall e,
  lc (abs e) ->
  body e.
Proof.
  intros e H.
  inversion H; subst.
  exists L; eauto.
Qed.

Lemma open_injective_rec : forall (x : atom) e1 e2 k,
  x `notin` (fv e1 `union` fv e2) ->
  open_rec k x e1 = open_rec k x e2 ->
  e1 = e2.
Proof with auto.
  induction e1; destruct e2; intros k H J; simpl in *; inversion J;
    try destruct (k === n);
    try destruct (k === n0);
    try congruence.
  assert (x <> a)... congruence.
  assert (x <> a)... congruence.
  f_equal. eapply IHe1; eauto.
  f_equal. eapply IHe1_1; eauto. eapply IHe1_2; eauto.
Qed.

Lemma open_injective : forall (x : atom) e1 e2,
  x `notin` (fv e1 `union` fv e2) ->
  open e1 x = open e2 x ->
  e1 = e2.
Proof.
  unfold open.
  eauto using open_injective_rec.
Qed.

Lemma level_promote : forall n e,
  level n e ->
  level (S n) e.
Proof.
  induction 1; auto.
Qed.

Lemma level_open : forall e n (x : atom),
  level n (open_rec n x e) ->
  level (S n) e.
Proof.
  induction e; intros n' x H; simpl in *; try solve [inversion H; eauto].
  destruct (n' === n); auto. subst; auto.
    inversion H. auto.
Qed.

Lemma level_of_lc : forall e,
  lc e -> level 0 e.
Proof with auto.
  induction 1...
  constructor.
  pick fresh x for L.
  apply level_open with (x := x).
  unfold open in *...
Qed.

Lemma open_close_inv_rec : forall e k (x : atom),
  level k e ->
  open_rec k x (close_rec k x e) = e.
Proof.
  induction e; intros k x H; inversion H; subst; simpl; f_equal; auto.
  destruct (k === n); auto.
    assert False by omega.
    intuition.
  destruct (x == a); simpl; intuition.
    destruct (k === k); congruence.
Qed.

Lemma open_close_inv : forall e (x : atom),
  lc e ->
  open (close e x) x = e.
Proof.
  unfold open.
  unfold close.
  auto using open_close_inv_rec, level_of_lc.
Qed.

Lemma close_fresh_rec : forall e k x,
  x `notin` fv (close_rec k x e).
Proof.
  induction e; intros k x; simpl; auto.
  destruct (x == a); simpl; auto.
Qed.

Lemma close_fresh : forall e x,
  x `notin` fv (close e x).
Proof.
  unfold close.
  auto using close_fresh_rec.
Qed.


(* *********************************************************************** *)
(** ** Automation *)

(** NOTE: "[Hint Constructors lc]" is declared above. *)

(** NOTE: [lc_open_from_body] interacts poorly with [lc_abs]. *)

Hint Resolve
  subst_lc
  lc_open_from_abs
  lc_abs_from_body body_from_lc_abs
  level_of_lc close_fresh_rec close_fresh.

Hint Extern 1 (body ?e) =>
  match goal with
    | H : lc (app ?e _) |- _ => inversion_clear H
    | H : lc (app _ ?e) |- _ => inversion_clear H
  end.

End Lam.
