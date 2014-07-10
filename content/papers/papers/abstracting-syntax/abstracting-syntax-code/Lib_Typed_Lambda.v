(** An implementation of the simply-typed lambda calculus
    parameterized over a set of base types and base constants.

    Author: Brian Aydemir. *)

Require Import Metatheory.
Declare Implicit Tactic auto.


(** We parameterize the sorts (types) for our simply-typed lambda
    calculus over a set of base sorts.  We define these sorts here in
    order to make it possible to define a signature for the base
    constants of the language. *)

Inductive lambda_sort (A : Set) : Set :=
  | lt_base : A -> lambda_sort A
  | lt_arrow : lambda_sort A -> lambda_sort A -> lambda_sort A.

Implicit Arguments lt_base [A].
Implicit Arguments lt_arrow [A].


(** We need the following in order to define the syntax of a language.

      - [const]: A set of base constants defining the constructors of
        the language.

      - [base_sort]: A set of base sorts defining the syntactic
        categories of the language.  Equality on these sorts must be
        decidable.

      - [signature]: Defines the arities/sorting of each of the base
        constants. *)

Module Type CONST.
  Parameter const : Set.
  Parameter base_sort : Set.
  Axiom eq_base_sort_dec : forall A B : base_sort, {A = B} + {A <> B}.
  Parameter signature : const -> lambda_sort base_sort.

  Hint Resolve eq_base_sort_dec.
End CONST.


(* *********************************************************************** *)
(** * Parameterized lambda calculus *)

(** We parameterize the lambda calculus over a set of base constants. *)

Module Lam (Const : CONST).

Import Const.


(* *********************************************************************** *)
(** ** Preliminaries *)

Notation Local sort := (lambda_sort base_sort).

(** Equality on sorts is decidable. *)

Definition eq_sort_dec : forall (A B : sort), {A = B} + {A <> B}.
decide equality.
Defined.

Hint Resolve eq_sort_dec.


(* *********************************************************************** *)
(** ** Pre-terms *)

Inductive syntax : Set :=
  | bvar : nat -> syntax
  | fvar : atom -> syntax
  | abs : sort -> syntax -> syntax
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
    | abs T e1 => abs T (open_rec (S k) u e1)
    | app e1 e2 => app (open_rec k u e1) (open_rec k u e2)
    | const v => e
  end.

Notation Local "{ k ~> u } t" := (open_rec k u t) (at level 67).

Definition open e u := open_rec 0 u e.

Fixpoint subst (z : atom) (u : syntax) (e : syntax) {struct e} : syntax :=
  match e with
    | bvar i => bvar i
    | fvar x => if x == z then u else (fvar x)
    | abs T e1 => abs T (subst z u e1)
    | app e1 e2 => app (subst z u e1) (subst z u e2)
    | _ => e
  end.

Notation Local "[ z ~> u ] e" := (subst z u e) (at level 68).

Fixpoint fv (e : syntax) {struct e} : atoms :=
  match e with
    | bvar i => {}
    | fvar x => singleton x
    | abs T e1 => (fv e1)
    | app e1 e2 => (fv e1) `union` (fv e2)
    | _ => {}
  end.

Fixpoint close_rec (k : nat) (x : atom) (e : syntax) {struct e} : syntax :=
  match e with
    | bvar i => bvar i
    | fvar y => if x == y then (bvar k) else (fvar y)
    | abs T e1 => abs T (close_rec (S k) x e1)
    | app e1 e2 => app (close_rec k x e1) (close_rec k x e2)
    | const c => const c
  end.

Definition close e x := close_rec 0 x e.


(* *********************************************************************** *)
(** ** Local closure *)

Notation Local "[ x ]" := (x :: nil) (at level 68).
Notation Local env := (list (atom * sort)).

(** The statement of [lc_const] is chosen such that it works well with
    Coq's automation facilities. *)

Inductive lc : env -> syntax -> sort -> Prop :=
  | lc_const : forall E c T,
      ok E ->
      signature c = T ->
      lc E (const c) T
  | lc_var : forall E x T,
      ok E ->
      binds x T E ->
      lc E (fvar x) T
  | lc_app : forall E  e1 e2 T1 T2,
      lc E e1 (lt_arrow T1 T2) ->
      lc E e2 T1 ->
      lc E (app e1 e2) T2
  | lc_abs : forall L E e T1 T2,
      (forall x, x `notin` L -> lc ([(x,T1)] ++ E) (open e x) T2) ->
      lc E (abs T1 e) (lt_arrow T1 T2).

Hint Constructors lc.

Definition lc' (s : syntax) : Prop :=
  exists E, exists T, lc E s T.

Hint Unfold lc'.

Definition body (E : env) (e : syntax) (T1 T2 : sort) : Prop :=
  exists L, forall x : atom, x `notin` L -> lc ([(x,T1)] ++ E) (open e x) T2.

Hint Unfold body.

Definition body' (e : syntax) : Prop :=
  exists E, exists T1, exists T2, body E e T1 T2.

Hint Unfold body'.

Inductive level : nat -> syntax -> Prop :=
  | level_bvar : forall n i,
      i < n ->
      level n (bvar i)
  | level_fvar : forall n x,
      level n (fvar x)
  | level_abs : forall T n e,
      level (S n) e ->
      level n (abs T e)
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
  lc' e ->
  e = {k ~> u} e.
Proof with auto.
  intros k u e [E [T H]].
  generalize dependent k.
  induction H; intros k; simpl; try solve [f_equal; auto].
  Case "abs".
    f_equal...
    pick fresh x for L.
    unfold open in *.
    apply (open_rec_lc_core e 0 x)...
Qed.

Lemma subst_open_rec : forall (x : atom) e1 e2 u k,
  lc' u ->
  [x ~> u] ({k ~> e2} e1) = {k ~> [x ~> u] e2} ([x ~> u] e1).
Proof with eauto.
  induction e1; intros e2 u k H; simpl in *; f_equal...
  Case "bvar".
    destruct (k === n)...
  Case "fvar".
    destruct (a == x); subst...
    eapply open_rec_lc...
Qed.

Lemma subst_open : forall (x : atom) e1 e2 u,
  lc' u ->
  [x ~> u] (open e1 e2) = open ([x ~> u] e1) ([x ~> u] e2).
Proof.
  intros.
  unfold open.
  eapply subst_open_rec; eauto.
Qed.

Lemma subst_open_var : forall (x y : atom) u e,
  y <> x ->
  lc' u ->
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

Lemma lc_regular : forall E e T,
  lc E e T ->
  ok E.
Proof.
  induction 1; eauto.
  pick fresh x for (L `union` dom E).
  pose proof (H0 x _) as K.
  inversion K; auto.
Qed.

Hint Local Resolve lc_regular.

Lemma lc_weakening : forall E F G e T,
  lc (F ++ E) e T ->
  ok (F ++ G ++ E) ->
  lc (F ++ G ++ E) e T.
Proof with simpl_env; eauto.
  intros E F G e T H.
  remember (F ++ E) as E'.
  generalize dependent F.
  induction H; intros F Eq J; subst...
  Case "lc_abs".
    pick fresh x excluding (L `union` dom (F ++ G ++ E)) and apply lc_abs.
    rewrite <- concat_assoc.
    apply H0...
Qed.

Lemma lc_weakening_head : forall E F e T,
  lc E e T ->
  ok (F ++ E) ->
  lc (F ++ E) e T.
Proof.
  intros.
  rewrite_env (nil ++ F ++ E).
  apply lc_weakening; simpl_env; auto.
Qed.

Lemma subst_lc : forall E F T U e u x,
  lc (F ++ [(x,U)] ++ E) e T ->
  lc E u U ->
  lc (F ++ E) ([x ~> u] e) T.
Proof with simpl_env; eauto.
  intros E F T U e u x H J.
  remember (F ++ [(x,U)] ++ E) as E'.
  generalize dependent F.
  induction H; intros F Eq; subst; simpl...
  Case "lc_var".
    destruct (x0 == x); subst...
    binds_get H0; subst...
    rewrite_env (nil ++ F ++ E).
    apply lc_weakening...
  Case "lc_abs".
    pick fresh y
      excluding (L `union` dom (F ++ E) `union` singleton x)
      and apply lc_abs.
    rewrite subst_open_var...
    rewrite <- concat_assoc.
    apply H0...
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

Lemma lc_open_from_body : forall L E e1 e2 T1 T2,
  (forall x : atom, x `notin` L -> lc ([(x,T1)] ++ E) (open e1 x) T2) ->
  lc E e2 T1 ->
  lc E (open e1 e2) T2.
Proof with eauto.
  intros L E e1 e2 T1 T2 H J.
  pick fresh x for (L `union` fv e1).
  rewrite (subst_intro x)...
  rewrite_env (nil ++ E).
  eapply subst_lc; simpl_env...
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
  lc' e -> level 0 e.
Proof with auto.
  intros e [E [T H]].
  induction H...
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
  lc' e ->
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
  lc_weakening lc_weakening_head
  level_of_lc close_fresh_rec close_fresh.

(** NOTE: The following hint is specifically for aiding applications
    of [lc_const]. *)

Hint Extern 1 (signature _ = _) =>
  simpl signature; try eapply refl_equal.

End Lam.
