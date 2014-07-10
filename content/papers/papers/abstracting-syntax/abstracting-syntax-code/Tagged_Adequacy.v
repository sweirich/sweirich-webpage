(** Adequacy of the tagged presentation with respect to our
    original locally nameless presentation.

    Author: Brian Aydemir (baydemir [at] cis.upenn.edu) *)


Require Export Omega.
Require Export Fsub_LetSum_Soundness.
Require Export Tagged_Soundness.


(** Because both developments use the same names, we use the module
    system to provide convenient shorthand prefixes that enable us to
    distinguish symbols.  The downside to doing this is that it seems
    to interfere with Coq's tactic automation, in ways I do not
    entirely understand. *)

Module A   := Fsub_LetSum_Definitions.
Module A'  := Fsub_LetSum_Infrastructure.
Module A'' := Fsub_LetSum_Soundness.
Module B   := Tagged_Definitions.
Module B'  := Tagged_Infrastructure.
Module B'' := Tagged_Soundness.


(* *********************************************************************** *)
(** * Other infrastructure *)

Set Implicit Arguments.

Fixpoint fv_spec (Q A : tag) (T : B.syntax A) {struct T} : atoms :=
  match T with
  | bvar _ J => {}
  | fvar B X =>
      if eq_tag_dec Q B then (singleton X) else {}
  | typ_top => {}
  | typ_arrow T1 T2 => (fv_spec Q T1) `union` (fv_spec Q T2)
  | typ_all T1 T2 => (fv_spec Q T1) `union` (fv_spec Q T2)
  | typ_sum T1 T2 => (fv_spec Q T1) `union` (fv_spec Q T2)
  | exp_abs V e1 => (fv_spec Q V) `union` (fv_spec Q e1)
  | exp_app e1 e2 => (fv_spec Q e1) `union` (fv_spec Q e2)
  | exp_tabs V e1 => (fv_spec Q V) `union` (fv_spec Q e1)
  | exp_tapp e1 V => (fv_spec Q V) `union` (fv_spec Q e1)
  | exp_let e1 e2 => (fv_spec Q e1) `union` (fv_spec Q e2)
  | exp_inl e1 => (fv_spec Q e1)
  | exp_inr e1 => (fv_spec Q e1)
  | exp_case e1 e2 e3 => (fv_spec Q e1) `union` (fv_spec Q e2) `union` (fv_spec Q e3)
  end.

Unset Implicit Arguments.


(* *********************************************************************** *)
(** * Tactics *)

(** We redefine some tactics so that they are effective in our current
    setting. *)

Ltac gather_atoms :=
  let A := gather_atoms_with (fun x : atoms => x) in
  let B := gather_atoms_with (fun x : atom => singleton x) in
  let C := gather_atoms_with (fun x : A.exp => A.fv_te x) in
  let D := gather_atoms_with (fun x : A.exp => A.fv_ee x) in
  let E := gather_atoms_with (fun x : A.typ => A.fv_tt x) in
  let F := gather_atoms_with (fun x : A.senv => dom x) in
  let G := gather_atoms_with (fun x : A.env => dom x) in
  let H := gather_atoms_with (fun x : B.senv => dom x) in
  let J := gather_atoms_with (fun x : B.env => dom x) in
  let K := gather_atoms_with (fun x : B.typ => B.fv x) in
  let K' := gather_atoms_with (fun x : B.exp => B.fv x) in
  let L1 := gather_atoms_with (fun x : B.typ => @fv_spec Typ Typ x) in
  let L2 := gather_atoms_with (fun x : B.typ => @fv_spec Exp Typ x) in
  let L3 := gather_atoms_with (fun x : B.exp => @fv_spec Typ Exp x) in
  let L4 := gather_atoms_with (fun x : B.exp => @fv_spec Exp Exp x) in
  constr:(A `union` B `union` C `union` D `union`
          E `union` F `union` G `union` H `union` J `union` K `union`
          K' `union` L1 `union` L2 `union` L3 `union` L4).

Tactic Notation "pick" "fresh" ident(x) :=
  let L := gather_atoms in (pick fresh x for L).

Tactic Notation
      "pick" "fresh" ident(atom_name) "and" "apply" constr(lemma) :=
  let L := gather_atoms in
  pick fresh atom_name excluding L and apply lemma.


(* *********************************************************************** *)
(** * Other infrastructure *)

(* *********************************************************************** *)
(** * Other infrastructure *)

(** We prove some induction principles for the tagged representation, becuase
    Coq does not automatically provide them. *)

Section Typ_induction.

Variables
  (P : typ -> Prop)
  (Hbvar : forall (n : nat), P (bvar n))
  (Hfvar : forall (a : atom), P (fvar a))
  (Htop : P typ_top)
  (Harrow : forall s : typ,
   P s -> forall s0 : typ, P s0 -> P (typ_arrow s s0))
  (Hall : forall s : typ,
   P s -> forall s0 : typ, P s0 -> P (typ_all s s0))
  (Hsum : forall s : typ,
   P s -> forall s0 : typ, P s0 -> P (typ_sum s s0)).

Lemma typ_ind_aux : forall (t : tag) (e : syntax t),
  (fun (t : tag) =>
    match t return syntax t -> Prop with
      | Typ => (fun t => P t)
      | Exp => (fun _ => True)
    end) t e.
Proof.
  induction e; eauto.
  destruct T; auto.
  destruct T; auto.
Qed.

Lemma typ_ind :
  forall (T : typ),  P T.
Proof.
  intros H.
  exact (typ_ind_aux _ H).
Qed.

End Typ_induction.

Section Exp_induction.
Variables
  (P : exp -> Prop)
  (Hbvar : forall (n : nat), P (bvar n))
  (Hfvar : forall (a : atom), P (fvar a))
  (Habs : forall s : typ, forall s0 : exp, P s0 -> P (exp_abs s s0))
  (Happ : forall s : exp,
   P s -> forall s0 : exp, P s0 -> P (exp_app s s0))
  (Htabs : forall s : typ,
   forall s0 : exp, P s0 -> P (exp_tabs s s0))
  (Htapp : forall s : exp, forall s0 : typ,
   P s -> P (exp_tapp s s0))
  (Hlet : forall s : exp,
   P s -> forall s0 : exp, P s0 -> P (exp_let s s0))
  (Hinl : forall s : exp, P s -> P (exp_inl s))
  (Hinr : forall s : exp, P s -> P (exp_inr s))
  (Hcase : forall s : exp,
   P s ->
   forall s0 : exp,
   P s0 ->
   forall s1 : exp, P s1 -> P (exp_case s s0 s1)).

Lemma exp_ind_aux : forall (t : tag) (e : syntax t),
  (fun (t : tag) =>
    match t return syntax t -> Prop with
      | Typ => (fun _ => True)
      | Exp => (fun e => P e)
    end) t e.
Proof.
  induction e; eauto.
  destruct T; auto.
  destruct T; auto.
Qed.

Lemma exp_ind :
  forall (e : exp), P e.
Proof.
  intros e.
  exact (exp_ind_aux _ e).
Qed.

End Exp_induction.

Section Typ_lc_induction.

Variables
  (P : typ -> Prop)
  (Hvar : forall (X : atom), P (typ_fvar X))
  (Htop : P typ_top)
  (Harrow : forall T1 T2 : typ,
   lc T1 -> P T1 -> lc T2 -> P T2 -> P (typ_arrow T1 T2))
  (Hall : forall (L : atoms) (T1 T2 : typ),
   lc T1 ->
   P T1 ->
   (forall X : atom, X `notin` L -> lc (open T2 (typ_fvar X))) ->
   (forall X : atom, X `notin` L -> P (open T2 (typ_fvar X))) ->
   P (typ_all T1 T2))
  (Hsum : forall T1 T2 : typ,
   lc T1 -> P T1 -> lc T2 -> P T2 -> P (typ_sum T1 T2)).

Lemma typ_lc_ind_aux : forall (t : tag) (e : syntax t),
  lc e ->
  (fun (t : tag) =>
    match t return syntax t -> Prop with
      | Typ => (fun t => P t)
      | Exp => (fun _ => True)
    end) t e.
Proof.
  induction 1; eauto.
  destruct A; auto.
Qed.

Lemma typ_lc_ind :
  forall (T : typ), lc T -> P T.
Proof.
  intros T H.
  exact (typ_lc_ind_aux _ T H).
Qed.

End Typ_lc_induction.

Section Exp_lc_induction.

Variables
  (P : exp -> Prop)
  (Hvar : forall (X : atom), P (exp_fvar X))
  (Habs : forall (L : atoms) (T : typ) (e1 : exp),
   lc T ->
   (forall x : atom, x `notin` L -> lc (open e1 (exp_fvar x))) ->
   (forall x : atom, x `notin` L -> P (open e1 (exp_fvar x))) ->
   P (exp_abs T e1))
  (Happ : forall e1 e2 : exp,
   lc e1 -> P e1 -> lc e2 -> P e2 -> P (exp_app e1 e2))
  (Htabs : forall (L : atoms) (T : typ) (e1 : exp),
   lc T ->
   (forall X : atom, X `notin` L -> lc (open e1 (typ_fvar X))) ->
   (forall X : atom, X `notin` L -> P (open e1 (typ_fvar X))) ->
   P (exp_tabs T e1))
  (Htapp : forall (e1 : exp) (V : typ),
   lc e1 -> P e1 -> lc V -> P (exp_tapp e1 V))
  (Hlet : forall (L : atoms) (e1 e2 : exp),
   lc e1 ->
   P e1 ->
   (forall x : atom, x `notin` L -> lc (open e2 (exp_fvar x))) ->
   (forall x : atom, x `notin` L -> P (open e2 (exp_fvar x))) ->
   P (exp_let e1 e2))
  (Hinl : forall e1 : exp, lc e1 -> P e1 -> P (exp_inl e1))
  (Hinr : forall e1 : exp, lc e1 -> P e1 -> P (exp_inr e1))
  (Hcase : forall (L : atoms) (e1 e2 e3 : exp),
   lc e1 ->
   P e1 ->
   (forall x : atom, x `notin` L -> lc (open e2 (exp_fvar x))) ->
   (forall x : atom, x `notin` L -> P (open e2 (exp_fvar x))) ->
   (forall x : atom, x `notin` L -> lc (open e3 (exp_fvar x))) ->
   (forall x : atom, x `notin` L -> P (open e3 (exp_fvar x))) ->
   P (exp_case e1 e2 e3)).

Lemma exp_lc_ind_aux : forall (t : tag) (e : syntax t),
  lc e ->
  (fun (t : tag) =>
    match t return syntax t -> Prop with
      | Typ => (fun _ => True)
      | Exp => (fun e => P e)
    end) t e.
Proof.
  induction 1; eauto.
  destruct A; auto.
Qed.

Lemma exp_lc_ind :
  forall (e : exp), lc e -> P e.
Proof.
  intros e H.
  exact (exp_lc_ind_aux _ e H).
Qed.

End Exp_lc_induction.

(** Opening a term with a variable is an injective operation if the
    variable is sufficiently fresh. *)

Lemma open_tt_injective_rec : forall T S k (X : atom),
  X `notin` (A.fv_tt T `union` A.fv_tt S) ->
  A.open_tt_rec k X T = A.open_tt_rec k X S ->
  T = S.
Proof.
  induction T; destruct S; intros k X H J; simpl in *;
    try congruence;
    try solve [ injection J; intros;
                f_equal; (eapply IHT1 || eapply IHT2); eauto 2; auto ];
    try destruct (k === n);
    try destruct (k === n0);
    try congruence.
  assert (X <> a) by auto. congruence.
  assert (X <> a) by auto. congruence.
Qed.

Lemma open_tt_injective : forall T S (X : atom),
  X `notin` (A.fv_tt T `union` A.fv_tt S) ->
  A.open_tt T X = A.open_tt S X ->
  T = S.
Proof.
  unfold A.open_tt.
  eauto using open_tt_injective_rec.
Qed.

Lemma open_te_injective_rec : forall e f k (X : atom),
  X `notin` (A.fv_te e `union` A.fv_te f) ->
  A.open_te_rec k X e = A.open_te_rec k X f ->
  e = f.
Proof with eauto.
  induction e; destruct f; intros k X H J; simpl in *;
    try solve [ inversion J; intros;
                f_equal;
                (eapply IHe
                  || eapply IHe1
                  || eapply IHe2
                  || eapply IHe3
                  || eapply open_tt_injective_rec);
                eauto 2; auto ].
Qed.

Lemma open_te_injective : forall e f (X : atom),
  X `notin` (A.fv_te e `union` A.fv_te f) ->
  A.open_te e X = A.open_te f X ->
  e = f.
Proof.
  unfold A.open_te.
  eauto using open_te_injective_rec.
Qed.

Lemma open_ee_injective_rec : forall e f k (X : atom),
  X `notin` (A.fv_ee e `union` A.fv_ee f) ->
  A.open_ee_rec k X e = A.open_ee_rec k X f ->
  e = f.
Proof with eauto.
  induction e; destruct f; intros k X H J; simpl in *;
    try congruence;
    try solve [ inversion J; intros;
                f_equal;
                (eapply IHe
                  || eapply IHe1
                  || eapply IHe2
                  || eapply IHe3
                  || eapply open_te_injective_rec);
                eauto 2; auto ];
    try destruct (k === n);
    try destruct (k === n0);
    try congruence.
  assert (X <> a) by auto. congruence.
  assert (X <> a) by auto. congruence.
Qed.

Lemma open_ee_injective : forall e f (X : atom),
  X `notin` (A.fv_ee e `union` A.fv_ee f) ->
  A.open_ee e X = A.open_ee f X ->
  e = f.
Proof.
  unfold A.open_ee.
  eauto using open_ee_injective_rec.
Qed.

Ltac repair_goal :=
  change typ_arrow with B.typ_arrow;
  change typ_all with B.typ_all;
  change typ_sum with B.typ_sum;
  change exp_abs with B.exp_abs;
  change exp_app with B.exp_app;
  change exp_tabs with B.exp_tabs;
  change exp_tapp with B.exp_tapp;
  change exp_let with B.exp_let;
  change exp_inl with B.exp_inl;
  change exp_inr with B.exp_inr;
  change exp_case with B.exp_case.

Lemma open_injective_rec :
  forall A B (T : B.syntax A) (S : B.syntax A) k (X : atom),
  X `notin` (B.fv T `union` B.fv S) ->
  B.open_rec k (@B.fvar B X) T = B.open_rec k (@B.fvar B X) S ->
  T = S.
Proof.
  induction T;
  try solve [
    destruct S; intros k X H J; simpl in *;
    try destruct (k === n); try destruct (k === n0);
    try destruct T; try destruct B;
    simpl in *; try congruence; try discriminate; inversion J;
    assert (X <> a) by auto; congruence
  | intros S; elim S using typ_ind; intros; simpl in *;
    try destruct (k === n); try destruct (k === n0);
    try destruct T; try destruct B;
    simpl in *; try congruence; try discriminate; try reflexivity;
    repair_goal;
    try solve [ inversion H2; intros; f_equal; intros; try congruence;
                (eapply IHT with (X := X)
                 || eapply IHT1 with (X := X)
                 || eapply IHT2 with (X := X)
                 || eapply IHT3 with (X := X));
                eauto 2; auto ]
  | intros S; elim S using exp_ind; intros; simpl in *;
    try destruct (k === n); try destruct (k === n0);
    try destruct T; try destruct B;
    simpl in *; try congruence; try discriminate; try reflexivity;
    repair_goal;
    try solve [ inversion H1; intros; f_equal; intros; try congruence;
                (eapply IHT with (X := X)
                 || eapply IHT1 with (X := X)
                 || eapply IHT2 with (X := X)
                 || eapply IHT3 with (X := X));
                eauto 2; auto ]
  | intros S; elim S using exp_ind; intros; simpl in *;
    try destruct (k === n); try destruct (k === n0);
    try destruct T; try destruct B;
    simpl in *; try congruence; try discriminate; try reflexivity;
    repair_goal;
    try solve [ inversion H2; intros; f_equal; intros; try congruence;
                (eapply IHT with (X := X)
                 || eapply IHT1 with (X := X)
                 || eapply IHT2 with (X := X)
                 || eapply IHT3 with (X := X));
                eauto 2; auto ]
  | intros S; elim S using exp_ind; intros; simpl in *;
    try destruct (k === n); try destruct (k === n0);
    try destruct T; try destruct B;
    simpl in *; try congruence; try discriminate; try reflexivity;
    repair_goal;
    try solve [ inversion H3; intros; f_equal; intros; try congruence;
                (eapply IHT with (X := X)
                 || eapply IHT1 with (X := X)
                 || eapply IHT2 with (X := X)
                 || eapply IHT3 with (X := X));
                eauto 2; auto ]
  ].
Qed.

Lemma open_injective : forall A B (T S : B.syntax A) (X : atom),
  X `notin` (B.fv T `union` B.fv S) ->
  B.open T (@B.fvar B X) = B.open S (@B.fvar B X) ->
  T = S.
Proof.
  unfold B.open.
  eauto using open_injective_rec.
Qed.

(** Lemmas about substitution. *)

Lemma subst_tt_fresh : forall Z (U : B.typ) (T : B.typ),
   Z `notin` fv_spec Typ T ->
   T = B.subst_tt Z U T.
Proof with auto*.
  intros Z U T.
  elim T using typ_ind; simpl; intros;
    destruct (eq_tag_dec Typ Typ); repair_goal; f_equal...
  Case "typ_fvar".
    destruct (a == Z)...
    absurd_hyp H; fsetdec.
Qed.

Lemma subst_et_fresh : forall Z (U : B.exp) (T : B.typ),
   Z `notin` fv_spec Exp T ->
   T = B.subst_tt Z U T.
Proof with auto*.
  intros Z U T.
  elim T using typ_ind; simpl; intros;
    destruct (eq_tag_dec Exp Typ); repair_goal; f_equal...
  Case "typ_fvar".
    destruct (a == Z)...
Qed.

Lemma subst_te_fresh : forall Z (U : B.typ) (T : B.exp),
   Z `notin` fv_spec Typ T ->
   T = B.subst_te Z U T.
Proof with auto*.
  intros Z U T.
  elim T using exp_ind; simpl; intros;
    destruct (eq_tag_dec Typ Exp); repair_goal; f_equal...
  Case "typ_fvar".
    destruct (a == Z)...
  rewrite <- subst_tt_fresh...
  rewrite <- subst_tt_fresh...
  rewrite <- subst_tt_fresh...
Qed.

Lemma subst_ee_fresh : forall Z (U : B.exp) (T : B.exp),
   Z `notin` fv_spec Exp T ->
   T = B.subst_ee Z U T.
Proof with auto*.
  intros Z U T.
  elim T using exp_ind; simpl; intros;
    destruct (eq_tag_dec Exp Exp); repair_goal; f_equal...
  Case "typ_fvar".
    destruct (a == Z)...
    absurd_hyp H; fsetdec.
  rewrite <- subst_et_fresh...
  rewrite <- subst_et_fresh...
  rewrite <- subst_et_fresh...
Qed.


(* *********************************************************************** *)
(** * Level *)


(* *********************************************************************** *)
(** ** Definitions *)

(** A term is at level [n] if the greatest index in the term is
    strictly less than [n]. *)

Inductive level_t : nat -> A.typ -> Prop :=
  | level_t_top : forall n,
      level_t n A.typ_top
  | level_t_bvar : forall n i,
      i < n ->
      level_t n (A.typ_bvar i)
  | level_t_fvar : forall n X,
      level_t n (A.typ_fvar X)
  | level_t_arrow : forall n T1 T2,
      level_t n T1 ->
      level_t n T2 ->
      level_t n (A.typ_arrow T1 T2)
  | level_t_all : forall n T1 T2,
      level_t n T1 ->
      level_t (S n) T2 ->
      level_t n (A.typ_all T1 T2)
  | level_t_sum : forall n T1 T2,
      level_t n T1 ->
      level_t n T2 ->
      level_t n (A.typ_sum T1 T2).

Hint Constructors level_t.

Inductive level_e : nat -> A.exp -> Prop :=
  | level_e_bvar : forall n i,
      i < n ->
      level_e n (A.exp_bvar i)
  | level_e_fvar : forall n X,
      level_e n (A.exp_fvar X)
  | level_e_abs : forall n T e,
      level_t n T ->
      level_e (S n) e ->
      level_e n (A.exp_abs T e)
  | level_e_app : forall n e1 e2,
      level_e n e1 ->
      level_e n e2 ->
      level_e n (A.exp_app e1 e2)
  | level_e_tabs : forall n T e,
      level_t n T ->
      level_e (S n) e ->
      level_e n (A.exp_tabs T e)
  | level_e_tapp : forall n e1 T2,
      level_e n e1 ->
      level_t n T2 ->
      level_e n (A.exp_tapp e1 T2)
  | level_e_let : forall n e1 e2,
      level_e n e1 ->
      level_e (S n) e2 ->
      level_e n (A.exp_let e1 e2)
  | level_e_inl : forall n e1,
      level_e n e1 ->
      level_e n (A.exp_inl e1)
  | level_e_inr : forall n e1,
      level_e n e1 ->
      level_e n (A.exp_inr e1)
  | level_e_case : forall n e1 e2 e3,
      level_e n e1 ->
      level_e (S n) e2 ->
      level_e (S n) e3 ->
      level_e n (A.exp_case e1 e2 e3).

Hint Constructors level_e.

Set Implicit Arguments.

Inductive level : forall A, nat -> B.syntax A -> Prop :=
  | level_bvar : forall A n i,
      i < n ->
      level n (@B.bvar A i)
  | level_fvar : forall A n X,
      level n (@B.fvar A X)
  | level_top : forall n,
      level n B.typ_top
  | level_arrow : forall n T1 T2,
      level n T1 ->
      level n T2 ->
      level n (B.typ_arrow T1 T2)
  | level_all : forall n T1 T2,
      level n T1 ->
      level (S n) T2 ->
      level n (B.typ_all T1 T2)
  | level_sum : forall n T1 T2,
      level n T1 ->
      level n T2 ->
      level n (B.typ_sum T1 T2)
  | level_abs : forall n T e,
      level n T ->
      level (S n) e ->
      level n (B.exp_abs T e)
  | level_app : forall n e1 e2,
      level n e1 ->
      level n e2 ->
      level n (B.exp_app e1 e2)
  | level_tabs : forall n T e,
      level n T ->
      level (S n) e ->
      level n (B.exp_tabs T e)
  | level_tapp : forall n e1 T2,
      level n e1 ->
      level n T2 ->
      level n (B.exp_tapp e1 T2)
  | level_let : forall n e1 e2,
      level n e1 ->
      level (S n) e2 ->
      level n (B.exp_let e1 e2)
  | level_inl : forall n e1,
      level n e1 ->
      level n (B.exp_inl e1)
  | level_inr : forall n e1,
      level n e1 ->
      level n (B.exp_inr e1)
  | level_case : forall n e1 e2 e3,
      level n e1 ->
      level (S n) e2 ->
      level (S n) e3 ->
      level n (B.exp_case e1 e2 e3).

Hint Constructors level.

Unset Implicit Arguments.

Hint Constructors level.


(* *********************************************************************** *)
(** ** Properties *)

(** A term at level [n] is also a term at level [(S n)]. *)

Lemma level_t_promote : forall n T,
  level_t n T ->
  level_t (S n) T.
Proof.
  induction 1; eauto.
Qed.

Hint Resolve level_t_promote.

Lemma level_e_promote : forall n e,
  level_e n e ->
  level_e (S n) e.
Proof.
  induction 1; eauto.
Qed.

Hint Resolve level_e_promote.

(** The following lemmas establish the relationship between the level
    of a term and opening. *)

Lemma level_t_open_tt : forall T2 n (X : atom),
  level_t n (A.open_tt_rec n X T2) ->
  level_t (S n) T2.
Proof.
  induction T2; intros n' X H; simpl in *; try solve [inversion H; eauto].
  destruct (n' === n); auto. subst; auto.
Qed.

Lemma level_e_open_te : forall e n (x : atom),
  level_e n (A.open_te_rec n x e) ->
  level_e (S n) e.
Proof.
  pose proof level_t_open_tt as J.
  induction e; intros n' X H; simpl in *; try solve [inversion H; eauto].
Qed.

Lemma level_e_open_ee : forall e n (x : atom),
  level_e n (A.open_ee_rec n x e) ->
  level_e (S n) e.
Proof.
  induction e; intros n' X H; simpl in *; try solve [inversion H; eauto].
  destruct (n' === n); auto. subst; auto.
Qed.

Lemma level_open : forall A B (T : B.syntax A) n (X : atom),
  level n (B.open_rec n (@B.fvar B X) T) ->
  level (S n) T.
Proof.
  induction T; intros n' X H; simpl in *; try solve [inversion H; eauto].
  destruct (n' === n); auto. subst; auto.
    inversion H. auto.
Qed.

(** Locally closed terms are at level 0. *)

Lemma level_t_of_type : forall T,
  A.type T -> level_t 0 T.
Proof with auto.
  induction 1...
  Case "type_all".
    constructor...
    pick fresh X for L.
    apply level_t_open_tt with (X := X).
    unfold A.open_tt in *...
Qed.

Hint Resolve level_t_of_type.

Lemma level_e_of_expr : forall e,
  A.expr e -> level_e 0 e.
Proof with auto.
  induction 1; auto;
    try solve [
      constructor; auto;
      pick fresh x for L;
      apply level_e_open_ee with (x := x);
      unfold A.open_ee in *; auto
    | constructor; auto;
      pick fresh x for L;
      apply level_e_open_te with (x := x);
      unfold A.open_te in *; auto
    ].
Qed.

Hint Resolve level_e_of_expr.

Lemma level_of_lc : forall A (T : syntax A),
  @B.lc A T -> @level A 0 T.
Proof with auto.
  induction 1; auto;
    try solve [
      constructor; auto;
      pick fresh X for L;
      eapply level_open with (X := X);
      unfold B.open in *; eauto
    ].
Qed.

Hint Resolve level_of_lc.


(* *********************************************************************** *)
(** * Closing *)


(* *********************************************************************** *)
(** ** Definitions *)

(** Closing replaces a free variable with an index.  The definition
    below assumes that [K] is greater than the greatest index
    appearing in [T]. *)

Fixpoint close_tt_rec (K : nat) (X : atom) (T : A.typ) {struct T} : A.typ :=
  match T with
    | A.typ_top => A.typ_top
    | A.typ_bvar n => A.typ_bvar n
    | A.typ_fvar Y => if X == Y then (A.typ_bvar K) else (A.typ_fvar Y)
    | A.typ_arrow T1 T2 =>
        A.typ_arrow (close_tt_rec K X T1) (close_tt_rec K X T2)
    | A.typ_all T1 T2 =>
        A.typ_all (close_tt_rec K X T1) (close_tt_rec (S K) X T2)
    | A.typ_sum T1 T2 =>
        A.typ_sum (close_tt_rec K X T1) (close_tt_rec K X T2)
  end.

Definition close_tt T X := close_tt_rec 0 X T.

Fixpoint close_te_rec (k : nat) (X : atom) (e : A.exp) {struct e} : A.exp :=
  match e with
    | A.exp_bvar n => A.exp_bvar n
    | A.exp_fvar x => A.exp_fvar x
    | A.exp_abs T e =>
        A.exp_abs (close_tt_rec k X T) (close_te_rec (S k) X e)
    | A.exp_app e1 e2 =>
        A.exp_app (close_te_rec k X e1) (close_te_rec k X e2)
    | A.exp_tabs T e =>
        A.exp_tabs (close_tt_rec k X T) (close_te_rec (S k) X e)
    | A.exp_tapp e1 T2 =>
        A.exp_tapp (close_te_rec k X e1) (close_tt_rec k X T2)
    | A.exp_let e1 e2 =>
        A.exp_let (close_te_rec k X e1) (close_te_rec (S k) X e2)
    | A.exp_inl e1 => A.exp_inl (close_te_rec k X e1)
    | A.exp_inr e1 => A.exp_inr (close_te_rec k X e1)
    | A.exp_case e1 e2 e3 =>
        A.exp_case (close_te_rec k X e1)
                   (close_te_rec (S k) X e2)
                   (close_te_rec (S k) X e3)
  end.

Definition close_te e X := close_te_rec 0 X e.

Fixpoint close_ee_rec (k : nat) (y : atom) (e : A.exp) {struct e} : A.exp :=
  match e with
    | A.exp_bvar n => A.exp_bvar n
    | A.exp_fvar x => if y == x then (A.exp_bvar k) else (A.exp_fvar x)
    | A.exp_abs T e =>
        A.exp_abs T (close_ee_rec (S k) y e)
    | A.exp_app e1 e2 =>
        A.exp_app (close_ee_rec k y e1) (close_ee_rec k y e2)
    | A.exp_tabs T e =>
        A.exp_tabs T (close_ee_rec (S k) y e)
    | A.exp_tapp e1 T2 =>
        A.exp_tapp (close_ee_rec k y e1) T2
    | A.exp_let e1 e2 =>
        A.exp_let (close_ee_rec k y e1) (close_ee_rec (S k) y e2)
    | A.exp_inl e1 => A.exp_inl (close_ee_rec k y e1)
    | A.exp_inr e1 => A.exp_inr (close_ee_rec k y e1)
    | A.exp_case e1 e2 e3 =>
        A.exp_case (close_ee_rec k y e1)
                   (close_ee_rec (S k) y e2)
                   (close_ee_rec (S k) y e3)
  end.

Definition close_ee e y := close_ee_rec 0 y e.

Set Implicit Arguments.

Fixpoint close_rec
  A B (K : nat) (X : atom) (t : B.syntax A) {struct t} : B.syntax A :=
  match t in B.syntax A return B.syntax A with
    | B.bvar _ n => B.bvar n
    | B.fvar A Y => if X == Y then @tagCheck B A (@B.bvar B K) (@B.fvar A Y) else (B.fvar Y)
    | B.typ_top => B.typ_top
    | B.typ_arrow T1 T2 => B.typ_arrow (close_rec B K X T1) (close_rec B K X T2)
    | B.typ_all T1 T2 => B.typ_all (close_rec B K X T1) (close_rec B (S K) X T2)
    | B.typ_sum T1 T2 => B.typ_sum (close_rec B K X T1) (close_rec B K X T2)
    | B.exp_abs T e => B.exp_abs (close_rec B K X T) (close_rec B (S K) X e)
    | B.exp_app e1 e2 => B.exp_app (close_rec B K X e1) (close_rec B K X e2)
    | B.exp_tabs T e => B.exp_tabs (close_rec B K X T) (close_rec B (S K) X e)
    | B.exp_tapp e T => B.exp_tapp (close_rec B K X e) (close_rec B K X T)
    | B.exp_let e1 e2 => B.exp_let (close_rec B K X e1) (close_rec B (S K) X e2)
    | B.exp_inl e1 => B.exp_inl (close_rec B K X e1)
    | B.exp_inr e1 => B.exp_inr (close_rec B K X e1)
    | B.exp_case e1 e2 e3 =>
        B.exp_case (close_rec B K X e1)
                   (close_rec B (S K) X e2)
                   (close_rec B (S K) X e3)
  end.

Definition close A B (T : B.syntax A) X := @close_rec A B 0 X T.

Unset Implicit Arguments.


(* *********************************************************************** *)
(** ** Properties *)

(** Opening and closing are inverses of each other under certain
    conditions. *)

Lemma open_tt_close_tt_inv_rec : forall (T : A.typ) (K : nat) (X : atom),
  level_t K T ->
  A.open_tt_rec K (A.typ_fvar X) (close_tt_rec K X T) = T.
Proof.
  induction T; intros K X H; inversion H; subst; simpl; f_equal; auto.
  destruct (K === n); auto.
    assert False by omega.
    intuition.
  destruct (X == a); simpl; intuition.
    destruct (K === K); congruence.
Qed.

Lemma open_tt_close_tt_inv : forall (T : A.typ) (X : atom),
  A.type T ->
  A.open_tt (close_tt T X) X = T.
Proof.
  unfold A.open_tt.
  unfold close_tt.
  auto using open_tt_close_tt_inv_rec.
Qed.

Lemma open_te_close_te_inv_rec : forall (e : A.exp) (K : nat) (X : atom),
  level_e K e ->
  A.open_te_rec K (A.typ_fvar X) (close_te_rec K X e) = e.
Proof.
  pose proof open_tt_close_tt_inv_rec as J.
  induction e; intros K X H; inversion H; subst;
    try solve [simpl; f_equal; auto].
Qed.

Lemma open_te_close_te_inv : forall (e : A.exp) (X : atom),
  A.expr e ->
  A.open_te (close_te e X) X = e.
Proof.
  unfold A.open_te.
  unfold close_te.
  auto using open_te_close_te_inv_rec.
Qed.

Lemma open_ee_close_ee_inv_rec : forall (e : A.exp) (k : nat) (x : atom),
  level_e k e ->
  A.open_ee_rec k (A.exp_fvar x) (close_ee_rec k x e) = e.
Proof.
  pose proof open_te_close_te_inv_rec as J2.
  induction e; intros K X H; inversion H; subst; simpl; f_equal; auto.
  destruct (K === n); auto.
    assert False by omega.
    intuition.
  destruct (X == a); simpl; intuition.
    destruct (K === K); congruence.
Qed.

Lemma open_ee_close_ee_inv : forall (e : A.exp) (x : atom),
  A.expr e ->
  A.open_ee (close_ee e x) x = e.
Proof.
  unfold A.open_ee.
  unfold close_ee.
  auto using open_ee_close_ee_inv_rec.
Qed.

Lemma open_close_inv_rec : forall A B (t : B.syntax A) (K : nat) (X : atom),
  level K t ->
  B.open_rec K (@B.fvar B X) (close_rec B K X t) = t.
Proof.
  induction t; intros K X H; inversion H; subst; simpl; f_equal; auto.
  destruct (K === n); auto.
    assert False by omega.
    intuition.
  destruct (X == a); simpl; intuition.
    destruct (K === K); try congruence.
    destruct B; destruct T; simpl; try congruence.
    destruct (K === K); try congruence.
    destruct (K === K); try congruence.
Qed.

Lemma open_close_inv : forall A B (e : B.syntax A) (X : atom),
  B.lc e ->
  @B.open B A (@close A B e X) (@fvar B X) = e.
Proof.
  unfold B.open.
  unfold close.
  auto using open_close_inv_rec.
Qed.

(** If we close a term with a particular name, that name will be fresh
    for the result. *)

Lemma close_tt_fresh_rec : forall (T : A.typ) (K : nat) (X : atom),
  X `notin` A.fv_tt (close_tt_rec K X T).
Proof.
  induction T; intros K X; simpl; auto.
  destruct (X == a); simpl; auto.
Qed.

Hint Resolve close_tt_fresh_rec.

Lemma close_tt_fresh : forall (T : A.typ) (X : atom),
  X `notin` A.fv_tt (close_tt T X).
Proof.
  unfold close_tt.
  auto using close_tt_fresh_rec.
Qed.

Hint Resolve close_tt_fresh.

Lemma close_te_fresh_te_rec : forall e1 (X : atom) (k : nat),
  X `notin` A.fv_te (close_te_rec k X e1).
Proof.
  induction e1; intros x k; simpl in *; auto.
Qed.

Lemma close_te_fresh_te : forall e1 (X : atom),
  X `notin` A.fv_te (close_te e1 X).
Proof.
  unfold close_te.
  auto using close_te_fresh_te_rec.
Qed.

Hint Resolve close_te_fresh_te.

Lemma close_ee_fresh_ee_rec : forall e1 (x : atom) (k : nat),
  x `notin` A.fv_ee (close_ee_rec k x e1).
Proof.
  induction e1; intros x k; simpl in *; auto.
  destruct (x == a); simpl; auto.
Qed.

Lemma close_ee_fresh_ee : forall e1 (x : atom),
  x `notin` A.fv_ee (close_ee e1 x).
Proof.
  unfold close_ee.
  auto using close_ee_fresh_ee_rec.
Qed.

Hint Resolve close_ee_fresh_ee.

Lemma close_fresh_rec : forall A B (t : B.syntax A) (K : nat) (X : atom),
  X `notin` @fv_spec B A (close_rec B K X t).
Proof.
  induction t; intros K X; try solve [simpl in *; auto].
  simpl in *.
  destruct (X == a); simpl; auto.
  destruct T; destruct B; simpl; auto.
  destruct (eq_tag_dec Exp Typ); auto.
  destruct (eq_tag_dec Typ Exp); auto.
  destruct (eq_tag_dec B T); auto.
Qed.

Hint Resolve close_fresh_rec.

Lemma close_fresh : forall A B (t : B.syntax A) (X : atom),
  X `notin` @fv_spec B A (close B t X).
Proof.
  unfold close.
  auto using close_fresh_rec.
Qed.

Hint Resolve close_fresh.


(* *********************************************************************** *)
(** * Bijection on senvs *)

(** In general, two developments may use different environments (given
    by the type [senv] in each development, according to our naming
    convention) for checking the well-formedness of Fsub types and
    expressions.  In order to define the bijection between Fsub terms,
    we need a bijection on [senv]s. *)


(* *********************************************************************** *)
(** ** Definition *)

(** The definition here is trivial because [A.senv] and [B.senv] are
    the same type.  The definition specifically does not check that
    the environments are ok; that must be done elsewhere. *)

Inductive senv_bijection : A.senv -> B.senv -> Prop :=
  | senv_bijection_refl : forall E,
      senv_bijection E E.

Hint Constructors senv_bijection.


(* *********************************************************************** *)
(** ** Properties *)

(** We define a tactic for simplifying [senv_bijection] propositions
    in the hypothesis list. *)

Ltac simplify_senv_bijection :=
  match goal with
    | H : senv_bijection ?E ?F |- _ =>
      inversion H; try subst F; try subst; clear H; simplify_senv_bijection
    | _ =>
      idtac
  end.

(** The bijection respects environment concatentation. *)

Lemma senv_bijection_app : forall E E' F F',
  senv_bijection E E' ->
  senv_bijection F F' ->
  senv_bijection (E ++ F) (E' ++ F').
Proof.
  intros.
  simplify_senv_bijection.
  auto.
Qed.

Hint Resolve senv_bijection_app.

Lemma senv_bijection_length : forall E E',
  senv_bijection E E' ->
  length E = length E'.
Proof.
  induction 1; simpl; try congruence.
Qed.

Lemma senv_bijection_head : forall E E' F F',
  senv_bijection (F ++ E) (F' ++ E') ->
  senv_bijection E E' ->
  senv_bijection F F'.
Proof.
  induction F as [|(y,b)]; induction F' as [|(z,c)];
    intros J1 J2; simpl_env in *; auto.
  Case "nil, cons".
    pose proof (senv_bijection_length _ _ J1) as J3.
    pose proof (senv_bijection_length _ _ J2) as J4.
    rewrite J4 in *.
    simpl in *; autorewrite with list in *.
    clear - J3.
    assert False; intuition.
  Case "cons, nil".
    pose proof (senv_bijection_length _ _ J1) as J3.
    pose proof (senv_bijection_length _ _ J2) as J4.
    rewrite <- J4 in *.
    simpl in *; autorewrite with list in *.
    clear - J3.
    assert False; intuition.
  Case "cons, cons".
    inversion J1; subst.
    SCase "Exp".
      inversion J1; subst.
      rewrite H1 in *.
      eauto.
Qed.


(* *********************************************************************** *)
(** * Bijection on types *)

(** We first define a relation on well-formed Fsub types and then show that
    the relation defines a bijection on such terms. *)


(* *********************************************************************** *)
(** ** Definition *)

Inductive typ_bijection : A.senv -> A.typ ->
                          B.senv -> B.typ -> Prop :=
  | typ_bijection_var : forall E E' X,
      ok E ->
      ok E' ->
      binds X Typ E ->
      binds X Typ E' ->
      senv_bijection E E' ->
      typ_bijection E (A.typ_fvar X) E' (B.fvar X)
  | typ_bijection_top : forall E E',
      ok E ->
      ok E' ->
      senv_bijection E E' ->
      typ_bijection E (A.typ_top) E' (B.typ_top)
  | typ_bijection_arrow : forall E E' T1 T1' T2 T2',
      typ_bijection E T1 E' T1' ->
      typ_bijection E T2 E' T2' ->
      typ_bijection E (A.typ_arrow T1 T2) E' (B.typ_arrow T1' T2')
  | typ_bijection_all : forall L E E' T1 T1' T2 T2',
      typ_bijection E T1 E' T1' ->
      (forall X : atom, X `notin` L ->
        typ_bijection ([(X,Typ)] ++ E)  (A.open_tt T2 X)
                      ([(X,Typ)] ++ E') (B.open T2' (B.typ_fvar X))) ->
      typ_bijection E (A.typ_all T1 T2) E' (B.typ_all T1' T2')
  | typ_bijection_sum : forall E E' T1 T1' T2 T2',
      typ_bijection E T1 E' T1' ->
      typ_bijection E T2 E' T2' ->
      typ_bijection E (A.typ_sum T1 T2) E' (B.typ_sum T1' T2').

Hint Constructors typ_bijection.


(* *********************************************************************** *)
(** ** Properties *)

(** The relation contains only related environments. *)

Lemma typ_bijection_senv : forall E E' T1 T2,
  typ_bijection E T1 E' T2 ->
  senv_bijection E E'.
Proof.
  induction 1; eauto.
Qed.

Hint Resolve typ_bijection_senv.

(** The relation contains only well-formed types. *)

Lemma typ_bijection_regular_1 : forall E E' T1 T2,
  typ_bijection E T1 E' T2 ->
  A.wf_typ E T1.
Proof.
  induction 1; econstructor; eauto.
Qed.

Hint Resolve typ_bijection_regular_1.

Lemma typ_bijection_regular_2 : forall E E' T1 T2,
  typ_bijection E T1 E' T2 ->
  B.wf_typ E' T2.
Proof.
  induction 1; econstructor; eauto.
Qed.

Hint Resolve typ_bijection_regular_2.

(** The bijection only holds for ok environments. *)

Lemma typ_bijection_ok_1 : forall E T1 E' T2,
  typ_bijection E T1 E' T2 ->
  ok E.
Proof.
  induction 1; eauto.
Qed.

Hint Resolve typ_bijection_ok_1.

Lemma typ_bijection_ok_2 : forall E E' T1 T2,
  typ_bijection E T1 E' T2 ->
  ok E'.
Proof.
  induction 1; eauto.
Qed.

Hint Resolve typ_bijection_ok_2.

(** Define a tactic to simplify proving well-formedness goals. *)

Ltac solve_lc_1 := try first [
    solve [apply lc_var]
  | solve [apply type_var]
  | solve [eapply B''.type_from_wf_typ; eapply typ_bijection_regular_2; eauto]
  | solve [eapply A''.type_from_wf_typ; eapply typ_bijection_regular_1; eauto]
  ].

(** Weakening holds for the bijection. *)

Lemma typ_bijection_weakening : forall E E' F F' G G' T1 T2,
  typ_bijection (F ++ E) T1 (F' ++ E') T2 ->
  senv_bijection E E' ->
  senv_bijection F F' ->
  senv_bijection G G' ->
  ok (F ++ G ++ E) ->
  ok (F' ++ G' ++ E') ->
  typ_bijection (F ++ G ++ E) T1 (F' ++ G' ++ E') T2.
Proof with simplify_senv_bijection; auto.
  intros E E' F F' G G' T1 T2 H.
  remember (F ++ E) as A.
  remember (F' ++ E') as A'.
  generalize dependent F.
  generalize dependent F'.
  induction H; intros; subst...
  Case "typ_bijection_all".
    pick fresh Z and apply typ_bijection_all...
    rewrite <- concat_assoc.
    apply H1; simpl_env...
Qed.

Lemma typ_bijection_weakening_head : forall E E' F F' T1 T2,
  typ_bijection E T1 E' T2 ->
  senv_bijection E E' ->
  senv_bijection F F' ->
  ok (F ++ E) ->
  ok (F' ++ E') ->
  typ_bijection (F ++ E) T1 (F' ++ E') T2.
Proof.
  intros.
  rewrite_env (nil ++ F ++ E).
  rewrite_env (nil ++ F' ++ E').
  apply typ_bijection_weakening; simpl_env; auto.
Qed.

Hint Resolve typ_bijection_weakening_head.

(** Substitution commutes with the bijection. *)

Lemma typ_bijection_subst : forall E E' F F' T1 T2 U1 U2 X,
  typ_bijection (F ++ [(X,Typ)] ++ E) T1 (F' ++ [(X,Typ)] ++ E') T2 ->
  typ_bijection E U1 E' U2 ->
  typ_bijection (F ++ E) (A.subst_tt X U1 T1) (F' ++ E') (B.subst X U2 T2).
Proof with solve_lc_1; auto.
  intros E E' F F' T1 T2 U1 U2 X H J.
  remember (F ++ [(X,Typ)] ++ E) as A.
  remember (F' ++ [(X,Typ)] ++ E') as A'.
  generalize dependent F.
  generalize dependent F'.
  induction H; intros; subst; simpl_env in *; simpl...
  Case "typ_bijection_var".
    assert (senv_bijection E E') by eauto using typ_bijection_senv.
    assert (senv_bijection ([(X,Common.Typ)]++E) ([(X,Typ)]++E')) by auto.
    destruct (X0 == X); subst.
      apply typ_bijection_weakening_head; eauto using senv_bijection_head.
      apply typ_bijection_var; eauto using senv_bijection_head.
  Case "typ_bijection_top".
    apply typ_bijection_weakening_head; eauto using senv_bijection_head.
  Case "typ_bijection_all".
    pick fresh Z and apply typ_bijection_all...
    do 2 rewrite <- concat_assoc.
    rewrite A'.subst_tt_open_tt_var...
    rewrite B'.subst_open_var...
Qed.

Lemma typ_bijection_rename : forall E E' T1 T2 (X Y : atom),
  X <> Y ->
  X `notin` (A.fv_tt T1 `union` fv_spec Typ T2) ->
  ok ([(Y,Typ)] ++ E) ->
  ok ([(Y,Typ)] ++ E') ->
  senv_bijection E E' ->
  typ_bijection ([(X,Typ)]++E) (A.open_tt T1 X) ([(X,Typ)]++E') (B.open T2 (B.typ_fvar X)) ->
  typ_bijection ([(Y,Typ)]++E) (A.open_tt T1 Y) ([(Y,Typ)]++E') (B.open T2 (B.typ_fvar Y)).
Proof with simplify_senv_bijection; solve_lc_1; simpl_env in *; auto.
  intros E E' T1 T2 X Y ? ? ? ? ? H.
  assert (Q : typ_bijection (nil ++ [(X,Typ)] ++ ([(Y,Typ)] ++ E))
                            (A.open_tt T1 X)
                            (nil ++ [(X,Typ)] ++ ([(Y,Typ)] ++ E'))
                            (B.open T2 (B.typ_fvar X))).
    simpl_env.
    assert (Q : ok ([(X,Typ)] ++ E)) by eauto.
    inversion Q; subst.
    apply typ_bijection_weakening...
  rewrite_env (nil ++ [(Y,Typ)] ++ E).
  rewrite_env (nil ++ [(Y,Typ)] ++ E').
  pose proof (typ_bijection_subst _ _ _ _ _ _ Y (B.typ_fvar Y) _ Q) as K.
  rewrite A'.subst_tt_open_tt in K...
  rewrite B'.subst_open in K...
  simpl in K.
  destruct (X == X); try solve [intuition].
  rewrite <- A'.subst_tt_fresh in K...
  rewrite <- subst_tt_fresh in K...
Qed.

(** Now prove that the bijection actually is a bijection. *)

Lemma typ_bijection_total : forall E T1,
  A.wf_typ E T1 ->
  exists E', exists T2, senv_bijection E E' /\ typ_bijection E T1 E' T2.
Proof with simplify_senv_bijection; solve_lc_1; eauto.
  induction 1...
  Case "type_arrow".
    destruct IHwf_typ1 as [? [? [? ?]]].
    destruct IHwf_typ2 as [? [? [? ?]]]...
  Case "type_all".
    pick fresh X.
    destruct IHwf_typ as [E' [T1' [? K1]]].
    lapply (H1 X); [ intros [E'' [T2' [? K2]]] | auto ].
    rewrite <- (open_close_inv _ Typ T2' X) in K2...
    exists E.
    exists (B.typ_all T1' (close Typ T2' X)).
    split...
    pick fresh Y and apply typ_bijection_all...
    eapply typ_bijection_rename with (X := X); auto.
      apply ok_push; eauto.
      apply ok_push; eauto.
  Case "type_sum".
    destruct IHwf_typ1 as [? [? [? ?]]].
    destruct IHwf_typ2 as [? [? [? ?]]]...
Qed.

Lemma typ_bijection_unique : forall E E' T1 T2 T3,
  typ_bijection E T1 E' T2 ->
  typ_bijection E T1 E' T3 ->
  T2 = T3.
Proof with auto.
  intros E E' T1 T2 T3 H.
  revert T3.
  induction H; intros T3 J; inversion J; subst; try solve [f_equal; auto].
  Case "typ_bijection_all".
    f_equal...
    pick fresh X.
    apply (open_injective _ Typ T2' T2'0 X)...
Qed.

Lemma typ_bijection_injective : forall E E' T1 T2 T3,
  typ_bijection E T1 E' T3 ->
  typ_bijection E T2 E' T3 -> T1 = T2.
Proof with auto.
  intros E E' T1 T2 T3 H.
  revert T2.
  induction H; intros S J; inversion J; subst; try solve [f_equal; auto].
  Case "typ_bijection_all".
    f_equal...
    pick fresh X.
    apply (open_tt_injective T2 T3 X)...
Qed.

Lemma typ_bijection_surjective : forall E' T2,
  B.wf_typ E' T2 ->
  exists E, exists T1, senv_bijection E E' /\ typ_bijection E T1 E' T2.
Proof with simplify_senv_bijection; solve_lc_1; eauto.
  induction 1...
  Case "wf_typ_arrow".
    destruct IHwf_typ1 as [? [? [? ?]]].
    destruct IHwf_typ2 as [? [? [? ?]]]...
  Case "wf_typ_all".
    pick fresh X.
    destruct IHwf_typ as [E' [T1' [? K1]]].
    lapply (H1 X); [ intros [? [T2' [? K2]]] | auto ].
    rewrite <- (open_tt_close_tt_inv T2' X) in K2...
    exists E'.
    exists (A.typ_all T1' (close_tt T2' X)).
    split...
    pick fresh Y and apply typ_bijection_all...
    eapply typ_bijection_rename with (X := X); auto.
      apply ok_push; eauto.
      apply ok_push; eauto.
  Case "wf_typ_sum".
    destruct IHwf_typ1 as [? [? [? ?]]].
    destruct IHwf_typ2 as [? [? [? ?]]]...
Qed.


(* *********************************************************************** *)
(** * Bijection on expressions *)

(** We first define a relation on well-formed Fsub expressions and
    then show that the relation defines a bijection on such terms. *)


(* *********************************************************************** *)
(** ** Definition *)

Inductive exp_bijection : A.senv -> A.exp ->
                          B.senv -> B.exp -> Prop :=
  | exp_bijection_var : forall E E' x,
      ok E ->
      ok E' ->
      senv_bijection E E' ->
      binds x Exp E ->
      binds x Exp E' ->
      exp_bijection E (A.exp_fvar x) E' (B.exp_fvar x)
  | exp_bijection_abs : forall L E E' T T' e e',
      typ_bijection E T E' T' ->
      (forall x : atom, x `notin` L ->
        exp_bijection ([(x,Exp)]++E) (A.open_ee e x) ([(x,Exp)]++E') (B.open e' (B.exp_fvar x))) ->
      exp_bijection E (A.exp_abs T e) E' (B.exp_abs T' e')
  | exp_bijection_app : forall E E' e1 e1' e2 e2',
      exp_bijection E e1 E' e1' ->
      exp_bijection E e2 E' e2' ->
      exp_bijection E (A.exp_app e1 e2) E' (B.exp_app e1' e2')
  | exp_bijection_tabs : forall L E E' T T' e e',
      typ_bijection E T E' T' ->
      (forall X : atom, X `notin` L ->
        exp_bijection ([(X,Typ)]++E) (A.open_te e X) ([(X,Typ)]++E') (B.open e' (B.typ_fvar X))) ->
      exp_bijection E (A.exp_tabs T e) E' (B.exp_tabs T' e')
  | exp_bijection_tapp : forall E E' e e' T T',
      exp_bijection E e E' e' ->
      typ_bijection E T E' T' ->
      exp_bijection E (A.exp_tapp e T) E' (B.exp_tapp e' T')
  | exp_bijection_let : forall L E E' e1 e1' e2 e2',
      exp_bijection E e1 E' e1' ->
      (forall x : atom, x `notin` L ->
        exp_bijection ([(x,Exp)]++E) (A.open_ee e2 x) ([(x,Exp)]++E') (B.open e2' (B.exp_fvar x))) ->
      exp_bijection E (A.exp_let e1 e2) E' (B.exp_let e1' e2')
  | exp_bijection_inl : forall E E' e e',
      exp_bijection E e E' e' ->
      exp_bijection E (A.exp_inl e) E' (B.exp_inl e')
  | exp_bijection_inr : forall E E' e e',
      exp_bijection E e E' e' ->
      exp_bijection E (A.exp_inr e) E' (B.exp_inr e')
  | exp_bijection_case : forall L E E' e1 e1' e2 e2' e3 e3',
      exp_bijection E e1 E' e1' ->
      (forall x : atom, x `notin` L ->
        exp_bijection ([(x,Exp)]++E) (A.open_ee e2 x) ([(x,Exp)]++E') (B.open e2' (B.exp_fvar x))) ->
      (forall x : atom, x `notin` L ->
        exp_bijection ([(x,Exp)]++E) (A.open_ee e3 x) ([(x,Exp)]++E') (B.open e3' (B.exp_fvar x))) ->
      exp_bijection E (A.exp_case e1 e2 e3) E' (B.exp_case e1' e2' e3').

Hint Constructors exp_bijection.


(* *********************************************************************** *)
(** ** Properties *)

(** The relation contains only related environments. *)

Lemma exp_bijection_senv : forall E E' T1 T2,
  exp_bijection E T1 E' T2 ->
  senv_bijection E E'.
Proof.
  induction 1; eauto.
Qed.

Hint Resolve exp_bijection_senv.

(** The relation contains only well-formed expressions. *)

Lemma exp_bijection_regular_1 : forall E E' e1 e2,
  exp_bijection E e1 E' e2 ->
  A.wf_exp E e1.
Proof.
  induction 1; econstructor; eauto.
Qed.

Hint Resolve exp_bijection_regular_1.

Lemma exp_bijection_regular_2 : forall E E' e1 e2,
  exp_bijection E e1 E' e2 ->
  B.wf_exp E' e2.
Proof.
  induction 1; econstructor; eauto.
Qed.

Hint Resolve exp_bijection_regular_2.

(** The bijection only holds for ok environments. *)

Lemma exp_bijection_ok_1 : forall E E' e1 e2,
  exp_bijection E e1 E' e2 ->
  ok E.
Proof.
  induction 1; eauto using typ_bijection_ok_1.
Qed.

Hint Resolve exp_bijection_ok_1.

Lemma exp_bijection_ok_2 : forall E E' e1 e2,
  exp_bijection E e1 E' e2 ->
  ok E'.
Proof.
  induction 1; eauto using typ_bijection_ok_2.
Qed.

Hint Resolve exp_bijection_ok_2.

(** Define a tactic to simplify proving well-formedness goals. *)

Ltac solve_lc_2 := try first [
    solve [solve_lc_1]
  | solve [apply expr_var]
  | solve [eapply B''.expr_from_wf_exp; eapply exp_bijection_regular_2; eauto]
  | solve [eapply A''.expr_from_wf_exp; eapply exp_bijection_regular_1; eauto]
  ].

(** Weakening holds for the bijection. *)

Lemma exp_bijection_weakening : forall E E' F F' G G' e1 e2,
  exp_bijection (F ++ E) e1 (F' ++ E') e2 ->
  senv_bijection E E' ->
  senv_bijection F F' ->
  senv_bijection G G' ->
  ok (F ++ G ++ E) ->
  ok (F' ++ G' ++ E') ->
  exp_bijection (F ++ G ++ E) e1 (F' ++ G' ++ E') e2.
Proof with simplify_senv_bijection; auto using typ_bijection_weakening.
  intros E E' F F' G G' e1 e2 H.
  remember (F ++ E) as A.
  remember (F' ++ E') as A'.
  generalize dependent F.
  generalize dependent F'.
  induction H; intros; subst...
  Case "exp_bijection_abs".
    pick fresh Z and apply exp_bijection_abs...
    rewrite <- concat_assoc.
    apply H1; simpl_env...
  Case "exp_bijection_tabs".
    pick fresh Z and apply exp_bijection_tabs...
    rewrite <- concat_assoc.
    apply H1; simpl_env...
  Case "exp_bijection_let".
    pick fresh Z and apply exp_bijection_let...
    rewrite <- concat_assoc.
    apply H1; simpl_env...
  Case "exp_bijection_case".
    pick fresh Z and apply exp_bijection_case...
    rewrite <- concat_assoc.
    apply H1; simpl_env...
    rewrite <- concat_assoc.
    apply H3; simpl_env...
Qed.

Lemma exp_bijection_weakening_head : forall E E' F F' e1 e2,
  exp_bijection E e1 E' e2 ->
  senv_bijection E E' ->
  senv_bijection F F' ->
  ok (F ++ E) ->
  ok (F' ++ E') ->
  exp_bijection (F ++ E) e1 (F' ++ E') e2.
Proof.
  intros.
  rewrite_env (nil ++ F ++ E).
  rewrite_env (nil ++ F' ++ E').
  apply exp_bijection_weakening; simpl_env; auto.
Qed.

Hint Resolve exp_bijection_weakening_head.

(** Substitution commutes with the bijection. *)

Lemma typ_bijection_strengthening : forall E E' F F' x T1 T2,
  senv_bijection E E' ->
  senv_bijection F F' ->
  typ_bijection (F ++ [(x,Exp)] ++ E) T1 (F' ++ [(x,Exp)] ++ E') T2 ->
  typ_bijection (F ++ E) T1 (F' ++ E') T2.
Proof with eauto 4.
  intros E E' F F' x T1 T2 ? ? H.
  remember (F ++ [(x,Exp)] ++ E) as A.
  remember (F' ++ [(x,Exp)] ++ E') as A'.
  generalize dependent F.
  generalize dependent F'.
  induction H; intros; subst...
  Case "typ_bijection_var".
    apply typ_bijection_var...
    binds_cases H2...
    binds_cases H3...
  Case "typ_bijection_abs".
    pick fresh Z and apply typ_bijection_all...
    do 2 rewrite <- concat_assoc.
    apply H2; simpl_env...
Qed.

Lemma exp_bijection_subst_ee : forall E E' F F' e1 e2 U1 U2 X,
  exp_bijection (F ++ [(X,Exp)] ++ E) e1 (F' ++ [(X,Exp)] ++ E') e2 ->
  exp_bijection E U1 E' U2 ->
  exp_bijection (F ++ E) (A.subst_ee X U1 e1) (F' ++ E') (B.subst X U2 e2).
Proof with solve_lc_2; eauto using typ_bijection_strengthening.
  intros E E' F F' e1 e2 U1 U2 X H J.
  remember (F ++ [(X,Exp)] ++ E) as A.
  remember (F' ++ [(X,Exp)] ++ E') as A'.
  generalize dependent F.
  generalize dependent F'.
  induction H; intros; subst; simpl_env in *; simpl...
  Case "exp_bijection_var".
    assert (senv_bijection E E') by eauto using typ_bijection_senv.
    assert (senv_bijection ([(X,Common.Exp)]++E) ([(X,Exp)]++E')) by auto.
    destruct (x == X); subst.
      apply exp_bijection_weakening_head; eauto 3 using senv_bijection_head.
      apply exp_bijection_var; eauto 4 using senv_bijection_head.
  Case "exp_bijection_abs".
    assert (senv_bijection E E') by eauto using typ_bijection_senv.
    assert (senv_bijection ([(X,Common.Exp)]++E) ([(X,Exp)]++E')) by auto.
    pick fresh Z and apply exp_bijection_abs.
      rewrite (B''.subst_fresh_exp_typ).
        eapply typ_bijection_strengthening; eauto 3.
          assert (senv_bijection E E') by eauto 3.
          pose proof (typ_bijection_senv _ _ _ _ H).
          eapply senv_bijection_head...
    do 2 rewrite <- concat_assoc.
    rewrite A'.subst_ee_open_ee_var...
    rewrite B'.subst_open_var...
  Case "exp_bijection_tabs".
    assert (senv_bijection E E') by eauto using typ_bijection_senv.
    assert (senv_bijection ([(X,Common.Typ)]++E) ([(X,Typ)]++E')) by auto.
    pick fresh Z and apply exp_bijection_tabs.
      rewrite (B''.subst_fresh_exp_typ).
        eapply typ_bijection_strengthening; eauto 3.
          assert (senv_bijection E E') by eauto 3.
          pose proof (typ_bijection_senv _ _ _ _ H).
          eapply senv_bijection_head...
    do 2 rewrite <- concat_assoc.
    rewrite A'.subst_ee_open_te_var...
    rewrite B'.subst_open_var...
  Case "exp_bijection_tapp".
    assert (senv_bijection E E') by eauto using typ_bijection_senv.
    assert (senv_bijection ([(X,Common.Exp)]++E) ([(X,Exp)]++E')) by auto.
    constructor. eauto.
      rewrite (B''.subst_fresh_exp_typ).
        eapply typ_bijection_strengthening; eauto 3.
          assert (senv_bijection E E') by eauto 3.
          pose proof (exp_bijection_senv _ _ _ _ H).
          eapply senv_bijection_head...
  Case "exp_bijection_let".
    pick fresh Z and apply exp_bijection_let...
    do 2 rewrite <- concat_assoc.
    rewrite A'.subst_ee_open_ee_var...
    rewrite B'.subst_open_var...
  Case "exp_bijection_case".
    pick fresh Z and apply exp_bijection_case...
    do 2 rewrite <- concat_assoc.
    rewrite A'.subst_ee_open_ee_var...
    rewrite B'.subst_open_var...
    do 2 rewrite <- concat_assoc.
    rewrite A'.subst_ee_open_ee_var...
    rewrite B'.subst_open_var...
Qed.

Lemma exp_bijection_subst_te : forall E E' F F' e1 e2 U1 U2 X,
  exp_bijection (F ++ [(X,Typ)] ++ E) e1 (F' ++ [(X,Typ)] ++ E') e2 ->
  typ_bijection E U1 E' U2 ->
  exp_bijection (F ++ E) (A.subst_te X U1 e1) (F' ++ E') (B.subst X U2 e2).
Proof with solve_lc_2; eauto using typ_bijection_subst.
  intros E E' F F' e1 e2 U1 U2 X H J.
  remember (F ++ [(X,Typ)] ++ E) as A.
  remember (F' ++ [(X,Typ)] ++ E') as A'.
  generalize dependent F.
  generalize dependent F'.
  induction H; intros; subst; simpl_env in *; simpl; eauto.
  Case "exp_bijection_var".
    destruct (x == X); subst.
    binds_get H2.
    assert (senv_bijection E E') by eauto using typ_bijection_senv.
    assert (senv_bijection ([(X,Common.Typ)]++E) ([(X,Typ)]++E')) by auto.
    apply exp_bijection_var; [ eauto | eauto | | eauto | eauto ].
      apply senv_bijection_app...
      eapply senv_bijection_head...
  Case "exp_bijection_abs".
    pick fresh Z and apply exp_bijection_abs...
    do 2 rewrite <- concat_assoc.
    rewrite A'.subst_te_open_ee_var...
    rewrite B'.subst_open_var...
  Case "exp_bijection_abs".
    pick fresh Z and apply exp_bijection_tabs...
    do 2 rewrite <- concat_assoc.
    rewrite A'.subst_te_open_te_var...
    rewrite B'.subst_open_var...
  Case "exp_bijection_tapp".
    constructor...
  Case "exp_bijection_let".
    pick fresh Z and apply exp_bijection_let...
    do 2 rewrite <- concat_assoc.
    rewrite A'.subst_te_open_ee_var...
    rewrite B'.subst_open_var...
  Case "exp_bijection_case".
    pick fresh Z and apply exp_bijection_case...
    do 2 rewrite <- concat_assoc.
    rewrite A'.subst_te_open_ee_var...
    rewrite B'.subst_open_var...
    do 2 rewrite <- concat_assoc.
    rewrite A'.subst_te_open_ee_var...
    rewrite B'.subst_open_var...
Qed.

Lemma exp_bijection_rename_open_ee : forall E E' e1 e2 (x y : atom),
  x <> y ->
  x `notin` (A.fv_ee e1 `union` fv_spec Exp e2) ->
  senv_bijection E E' ->
  ok ([(y,Exp)]++E) ->
  ok ([(y,Exp)]++E') ->
  exp_bijection ([(x,Exp)]++E) (A.open_ee e1 x) ([(x,Exp)]++E') (B.open e2 (B.exp_fvar x)) ->
  exp_bijection ([(y,Exp)]++E) (A.open_ee e1 y) ([(y,Exp)]++E') (B.open e2 (B.exp_fvar y)).
Proof with simplify_senv_bijection; solve_lc_2; auto.
  intros E E' e1 e2 x y ? ? ? ? ? H.
  assert (Q : exp_bijection (nil ++ [(x,Exp)] ++ ([(y,Exp)] ++ E))
                            (A.open_ee e1 x)
                            (nil ++ [(x,Exp)] ++ ([(y,Exp)] ++ E'))
                            (B.open e2 (B.exp_fvar x))).
    simpl_env.
    assert (Q : ok ([(x,Exp)]++E)) by eauto.
    inversion Q; subst.
    apply exp_bijection_weakening...
  rewrite_env (nil ++ [(y,Exp)] ++ E).
  rewrite_env (nil ++ [(y,Exp)] ++ E').
  pose proof (exp_bijection_subst_ee _ _ _ _ _ _ y (B.exp_fvar y) _ Q) as K.
  rewrite A'.subst_ee_open_ee in K...
  rewrite B'.subst_open in K...
  simpl in K.
  destruct (x == x); try solve [intuition].
  rewrite <- A'.subst_ee_fresh in K...
  rewrite <- subst_ee_fresh in K...
  apply K; simpl_env in *...
Qed.

Lemma exp_bijection_rename_open_te : forall E E' e1 e2 (x y : atom),
  x <> y ->
  x `notin` (A.fv_te e1 `union` fv_spec Typ e2) ->
  senv_bijection E E' ->
  ok ([(y,Typ)]++E) ->
  ok ([(y,Typ)]++E') ->
  exp_bijection ([(x,Typ)]++E) (A.open_te e1 x) ([(x,Typ)]++E') (B.open e2 (B.typ_fvar x)) ->
  exp_bijection ([(y,Typ)]++E) (A.open_te e1 y) ([(y,Typ)]++E') (B.open e2 (B.typ_fvar y)).
Proof with simplify_senv_bijection; solve_lc_2; auto.
  intros E E' e1 e2 x y ? ? ? ? ? H.
  inversion H3; subst.
  assert (Q : exp_bijection (nil ++ [(x,Typ)] ++ ([(y,Typ)] ++ E))
                            (A.open_te e1 x)
                            (nil ++ [(x,Typ)] ++ ([(y,Typ)] ++ E'))
                            (B.open e2 (B.typ_fvar x))).
    simpl_env.
    assert (Q : ok ([(x,Typ)]++E)) by eauto.
    inversion Q; subst.
    apply exp_bijection_weakening...
  rewrite_env (nil ++ [(y,Typ)] ++ E).
  rewrite_env (nil ++ [(y,Typ)] ++ E').
  pose proof (exp_bijection_subst_te _ _ _ _ _ _ y (B.typ_fvar y) _ Q) as K.
  rewrite A'.subst_te_open_te in K...
  rewrite B'.subst_open in K...
  simpl in K.
  destruct (x == x); try solve [intuition].
  rewrite <- A'.subst_te_fresh in K...
  rewrite <- subst_te_fresh in K...
  apply K; simpl_env in *...
Qed.

(** Now prove that the bijection actually is a bijection. *)

Lemma exp_bijection_total : forall E e,
  A.wf_exp E e ->
  exists E', exists e', senv_bijection E E' /\ exp_bijection E e E' e'.
Proof with simplify_senv_bijection; solve_lc_2; eauto.
  induction 1...
  Case "exp_abs".
    pick fresh x.
    destruct (typ_bijection_total _ _ H) as [E' [T' [? K1]]].
    lapply (H1 x); [ intros [E'' [e' [? K2]]] | auto ].
    rewrite <- (open_close_inv _ Exp e' x) in K2...
    exists E.
    exists (B.exp_abs T' (close Exp e' x)).
    split...
    pick fresh y and apply exp_bijection_abs...
    eapply exp_bijection_rename_open_ee with (x := x); auto.
      apply ok_push; auto. eapply typ_bijection_ok_1; eauto.
      apply ok_push; auto. eapply typ_bijection_ok_1; eauto.
  Case "exp_app".
    destruct IHwf_exp1 as [? [? [? ?]]].
    destruct IHwf_exp2 as [? [? [? ?]]]...
  Case "exp_tabs".
    pick fresh x.
    destruct (typ_bijection_total _ _ H) as [E' [T' [? K1]]].
    lapply (H1 x); [ intros [E'' [e' [? K2]]] | auto ].
    rewrite <- (open_close_inv _ Typ e' x) in K2...
    exists E.
    exists (B.exp_tabs T' (close Typ e' x)).
    split...
    pick fresh y and apply exp_bijection_tabs...
    eapply exp_bijection_rename_open_te with (x := x); auto.
      apply ok_push; auto. eapply typ_bijection_ok_1; eauto.
      apply ok_push; auto. eapply typ_bijection_ok_1; eauto.
  Case "exp_tapp".
    destruct (typ_bijection_total _ _ H0) as [E' [T' [? K1]]].
    destruct IHwf_exp as [? [? [? ?]]]...
  Case "exp_let".
    pick fresh x.
    destruct IHwf_exp as [E' [e1' [? K1]]].
    lapply (H1 x); [ intros [E'' [e' [? K2]]] | auto ].
    rewrite <- (open_close_inv _ Exp e' x) in K2...
    exists E.
    exists (B.exp_let e1' (close Exp e' x)).
    split...
    pick fresh y and apply exp_bijection_let...
    eapply exp_bijection_rename_open_ee with (x := x); auto.
      apply ok_push; auto. eapply exp_bijection_ok_1; eauto.
      apply ok_push; auto. eapply exp_bijection_ok_1; eauto.
  Case "exp_inl".
    destruct IHwf_exp as [? [? [? ?]]]...
  Case "exp_inr".
    destruct IHwf_exp as [? [? [? ?]]]...
  Case "exp_case".
    pick fresh x.
    destruct IHwf_exp as [? [e1' [? K1]]].
    lapply (H1 x); [ intros [? [e2' [? K2]]] | auto ].
    rewrite <- (open_close_inv _ Exp e2' x) in K2...
    lapply (H3 x); [ intros [? [e3' [? K3]]] | auto ].
    rewrite <- (open_close_inv _ Exp e3' x) in K3...
    exists E.
    exists (B.exp_case e1' (close Exp e2' x) (close Exp e3' x)).
    split...
    pick fresh y and apply exp_bijection_case...
    eapply exp_bijection_rename_open_ee with (x := x); auto.
      apply ok_push; auto. eapply exp_bijection_ok_1; eauto.
      apply ok_push; auto. eapply exp_bijection_ok_1; eauto.
    eapply exp_bijection_rename_open_ee with (x := x); auto.
      apply ok_push; auto. eapply exp_bijection_ok_1; eauto.
      apply ok_push; auto. eapply exp_bijection_ok_1; eauto.
Qed.

Lemma exp_bijection_unique : forall E E' e1 e2 e3,
  exp_bijection E e1 E' e2 ->
  exp_bijection E e1 E' e3 ->
  e2 = e3.
Proof with eauto using typ_bijection_unique.
  intros E E' e1 e2 e3 H.
  revert e3.
  induction H; intros e3'' J; inversion J; subst;
    try solve [f_equal; eauto 3 using typ_bijection_unique].
  Case "exp_bijection_abs".
    f_equal...
    pick fresh x.
    apply (open_injective _ Exp e' e'0 x)...
  Case "exp_bijection_tabs".
    f_equal...
    pick fresh x.
    apply (open_injective _ Typ e' e'0 x)...
  Case "exp_bijection_let".
    f_equal...
    pick fresh x.
    apply (open_injective _ Exp e2' e2'0 x)...
  Case "exp_bijection_case".
    f_equal...
    pick fresh x.
    apply (open_injective _ Exp e2' e2'0 x)...
    pick fresh x.
    apply (open_injective _ Exp e3' e3'0 x)...
Qed.

Lemma exp_bijection_injective : forall E E' e1 e2 e3,
  exp_bijection E e1 E' e3 ->
  exp_bijection E e2 E' e3 ->
  e1 = e2.
Proof with eauto using typ_bijection_injective.
  intros E E' e1 e2 e3 H.
  revert e2.
  induction H; intros f J; inversion J; subst;
    try solve [f_equal; eauto 3 using typ_bijection_injective].
  Case "exp_bijection_abs".
    f_equal...
    pick fresh x.
    apply (open_ee_injective e e0 x)...
  Case "exp_bijection_tabs".
    f_equal...
    pick fresh x.
    apply (open_te_injective e e0 x)...
  Case "exp_bijection_let".
    f_equal...
    pick fresh x.
    apply (open_ee_injective e2 e3 x)...
  Case "exp_bijection_case".
    f_equal...
    pick fresh x.
    apply (open_ee_injective e2 e4 x)...
    pick fresh x.
    apply (open_ee_injective e3 e5 x)...
Qed.

Lemma exp_bijection_surjective : forall E' e2,
  B.wf_exp E' e2 ->
  exists E, exists e1, senv_bijection E E' /\ exp_bijection E e1 E' e2.
Proof with simplify_senv_bijection; solve_lc_2; eauto.
  induction 1...
  Case "wf_exp_abs".
    pick fresh x.
    destruct (typ_bijection_surjective _ _ H) as [E' [T' [? K1]]].
    lapply (H1 x); [ intros [? [e1' [? K2]]] | auto ].
    rewrite <- (open_ee_close_ee_inv e1' x) in K2...
    exists E'.
    exists (A.exp_abs T' (close_ee e1' x)).
    split...
    pick fresh y and apply exp_bijection_abs...
    apply exp_bijection_rename_open_ee with (x := x); auto.
      apply ok_push; auto. eapply typ_bijection_ok_1; eauto.
      apply ok_push; auto. eapply typ_bijection_ok_1; eauto.
  Case "wf_exp_app".
    destruct IHwf_exp1 as [? [? [? ?]]].
    destruct IHwf_exp2 as [? [? [? ?]]]...
  Case "wf_exp_abs".
    pick fresh x.
    destruct (typ_bijection_surjective _ _ H) as [E' [T' [? K1]]].
    lapply (H1 x); [ intros [? [e1' [? K2]]] | auto ].
    rewrite <- (open_te_close_te_inv e1' x) in K2...
    exists E'.
    exists (A.exp_tabs T' (close_te e1' x)).
    split...
    pick fresh y and apply exp_bijection_tabs...
    apply exp_bijection_rename_open_te with (x := x); auto.
      apply ok_push; auto. eapply typ_bijection_ok_1; eauto.
      apply ok_push; auto. eapply typ_bijection_ok_1; eauto.
  Case "wf_exp_tapp".
    destruct (typ_bijection_surjective _ _ H0) as [? [T' [? K1]]].
    destruct IHwf_exp as [? [? [? ?]]]...
  Case "wf_exp_let".
    pick fresh x.
    destruct IHwf_exp as [E' [T' [? K1]]].
    lapply (H1 x); [ intros [? [e1' [? K2]]] | auto ].
    rewrite <- (open_ee_close_ee_inv e1' x) in K2...
    exists E'.
    exists (A.exp_let T' (close_ee e1' x)).
    split...
    pick fresh y and apply exp_bijection_let...
    eapply exp_bijection_rename_open_ee with (x := x); auto.
      apply ok_push; auto. eapply exp_bijection_ok_1; eauto.
      apply ok_push; auto. eapply exp_bijection_ok_1; eauto.
  Case "exp_inl".
    destruct IHwf_exp as [? [? [? ?]]]...
  Case "exp_inr".
    destruct IHwf_exp as [? [? [? ?]]]...
  Case "wf_exp_case".
    pick fresh x.
    destruct IHwf_exp as [E' [e1' [? K1]]].
    lapply (H1 x); [ intros [? [e2' [? K2]]] | auto ].
    rewrite <- (open_ee_close_ee_inv e2' x) in K2...
    lapply (H3 x); [ intros [? [e3' [? K3]]] | auto ].
    rewrite <- (open_ee_close_ee_inv e3' x) in K3...
    exists E'.
    exists (A.exp_case e1' (close_ee e2' x) (close_ee e3' x)).
    split...
    pick fresh y and apply exp_bijection_case...
    eapply exp_bijection_rename_open_ee with (x := x); auto.
      apply ok_push; auto. eapply exp_bijection_ok_1; eauto.
      apply ok_push; auto. eapply exp_bijection_ok_1; eauto.
    eapply exp_bijection_rename_open_ee with (x := x); auto.
      apply ok_push; auto. eapply exp_bijection_ok_1; eauto.
      apply ok_push; auto. eapply exp_bijection_ok_1; eauto.
Qed.


(* *********************************************************************** *)
(** * Bijection on environments *)


(* *********************************************************************** *)
(** ** Definition *)

Inductive env_bijection : A.env -> B.env -> Prop :=
  | env_bijection_nil :
      env_bijection nil nil
  | env_bijection_typ : forall E E' x T T',
      x `notin` (dom E `union` dom E') ->
      typ_bijection (A.to_senv E) T (B.to_senv E') T' ->
      env_bijection E E' ->
      env_bijection ([(x, A.bind_typ T)] ++ E) ([(x, B.bind_typ T')] ++ E')
  | env_bijection_sub : forall E E' X T T',
      X `notin` (dom E `union` dom E') ->
      typ_bijection (A.to_senv E) T (B.to_senv E') T' ->
      env_bijection E E' ->
      env_bijection ([(X, A.bind_sub T)] ++ E) ([(X, B.bind_sub T')] ++ E').


(* *********************************************************************** *)
(** ** Properties *)

Lemma env_bijection_senv : forall E E',
  env_bijection E E' ->
  senv_bijection (A.to_senv E) (B.to_senv E').
Proof.
  induction 1; simpl in *; auto.
  simplify_senv_bijection. rewrite H4. auto.
  simplify_senv_bijection. rewrite H4. auto.
Qed.

Hint Resolve env_bijection_senv.

Lemma env_bijection_binds_sub_1 : forall E E' X U,
  binds X (A.bind_sub U) E ->
  env_bijection E E' ->
  exists U', typ_bijection (A.to_senv E) U (B.to_senv E') U' /\
             binds X (B.bind_sub U') E'.
Proof with eauto.
  induction E as [ | (x,T) ]; intros F' X U H J.
  binds_cases H.
  simpl_env in *.
  binds_cases H.
  Case "tail".
    inversion J; subst; simpl_env.
    SCase "bind_typ".
      destruct (IHE E' _ _ H0) as [U' [? ?]]...
      exists U'.
      split; auto.
      apply typ_bijection_weakening_head; auto.
        apply ok_push; eauto.
        apply ok_push; eauto.
    SCase "bind_sub".
      destruct (IHE E' _ _ H0) as [U' [? ?]]...
      exists U'.
      split; auto.
      apply typ_bijection_weakening_head; auto.
        apply ok_push; eauto.
        apply ok_push; eauto.
  Case "head".
    inversion J; subst; simpl_env.
    SCase "bind_typ".
      inversion J.
    SCase "bind_sub".
      inversion J; subst; simpl_env.
      exists T'.
      split; auto.
      simpl; simpl_env.
      apply typ_bijection_weakening_head; auto.
        apply ok_push; eauto.
        apply ok_push; eauto.
Qed.

Lemma env_bijection_binds_sub_2 : forall E' E X U',
  binds X (B.bind_sub U') E' ->
  env_bijection E E' ->
  exists U, typ_bijection (A.to_senv E) U (B.to_senv E') U' /\
             binds X (A.bind_sub U) E.
Proof with eauto.
  induction E' as [ | (x,T) ]; intros F X U' H J.
  binds_cases H.
  simpl_env in *.
  binds_cases H.
  Case "tail".
    inversion J; subst; simpl_env.
    SCase "bind_typ".
      destruct (IHE' E _ _ H0) as [U [? ?]]...
      exists U.
      split; auto.
      apply typ_bijection_weakening_head; auto.
        apply ok_push; eauto.
        apply ok_push; eauto.
    SCase "bind_sub".
      destruct (IHE' E _ _ H0) as [U [? ?]]...
      exists U.
      split; auto.
      apply typ_bijection_weakening_head; auto.
        apply ok_push; eauto.
        apply ok_push; eauto.
  Case "head".
    inversion J; subst; simpl_env.
    SCase "bind_typ".
      inversion J.
    SCase "bind_sub".
      inversion J; subst; simpl_env.
      exists T0.
      split; auto.
      simpl; simpl_env.
      apply typ_bijection_weakening_head; auto.
        apply ok_push; eauto.
        apply ok_push; eauto.
Qed.

Lemma env_bijection_binds_typ_1 : forall E E' X U,
  binds X (A.bind_typ U) E ->
  env_bijection E E' ->
  exists U', typ_bijection (A.to_senv E) U (B.to_senv E') U' /\
             binds X (B.bind_typ U') E'.
Proof with eauto.
  induction E as [ | (x,T) ]; intros F' X U H J.
  binds_cases H.
  simpl_env in *.
  binds_cases H.
  Case "tail".
    inversion J; subst; simpl_env.
    SCase "bind_typ".
      destruct (IHE E' _ _ H0) as [U' [? ?]]...
      exists U'.
      split; auto.
      apply typ_bijection_weakening_head; auto.
        apply ok_push; eauto.
        apply ok_push; eauto.
    SCase "bind_sub".
      destruct (IHE E' _ _ H0) as [U' [? ?]]...
      exists U'.
      split; auto.
      apply typ_bijection_weakening_head; auto.
        apply ok_push; eauto.
        apply ok_push; eauto.
  Case "head".
    inversion J; subst; simpl_env.
    SCase "bind_typ".
      inversion J; subst; simpl_env.
      exists T'.
      split; auto.
      simpl; simpl_env.
      apply typ_bijection_weakening_head; auto.
        apply ok_push; eauto.
        apply ok_push; eauto.
    SCase "bind_sub".
      inversion J.
Qed.

Lemma env_bijection_binds_typ_2 : forall E' E X U',
  binds X (B.bind_typ U') E' ->
  env_bijection E E' ->
  exists U, typ_bijection (A.to_senv E) U (B.to_senv E') U' /\
             binds X (A.bind_typ U) E.
Proof with eauto.
  induction E' as [ | (x,T) ]; intros F X U' H J.
  binds_cases H.
  simpl_env in *.
  binds_cases H.
  Case "tail".
    inversion J; subst; simpl_env.
    SCase "bind_typ".
      destruct (IHE' E _ _ H0) as [U [? ?]]...
      exists U.
      split; auto.
      apply typ_bijection_weakening_head; auto.
        apply ok_push; eauto.
        apply ok_push; eauto.
    SCase "bind_sub".
      destruct (IHE' E _ _ H0) as [U [? ?]]...
      exists U.
      split; auto.
      apply typ_bijection_weakening_head; auto.
        apply ok_push; eauto.
        apply ok_push; eauto.
  Case "head".
    inversion J; subst; simpl_env.
    SCase "bind_typ".
      inversion J; subst; simpl_env.
      exists T0.
      split; auto.
      simpl; simpl_env.
      apply typ_bijection_weakening_head; auto.
        apply ok_push; eauto.
        apply ok_push; eauto.
    SCase "bind_sub".
      inversion J.
Qed.

(** The relation holds for only well-formed environments. *)

Lemma env_bijection_wf_env_1 : forall E E',
  env_bijection E E' ->
  A.wf_env E.
Proof.
  induction 1; eauto.
Qed.

Hint Resolve env_bijection_wf_env_1.

Lemma env_bijection_wf_env_2 : forall E E',
  env_bijection E E' ->
  B.wf_env E'.
Proof.
  induction 1; eauto.
Qed.

Hint Resolve env_bijection_wf_env_2.


(* *********************************************************************** *)
(** * Relations derive the same judgements *)

(** These first lemmas are trivial, given our definitions. *)

Lemma wf_typ_bijection : forall E E' T T',
  typ_bijection E T E' T' ->
  (A.wf_typ E T <-> B.wf_typ E' T').
Proof.
  intuition eauto.
Qed.

Lemma wf_exp_bijection : forall E E' e e',
  exp_bijection E e E' e' ->
  (A.wf_exp E e <-> B.wf_exp E' e').
Proof.
  intuition eauto.
Qed.

Lemma wf_env_bijection : forall E E',
  env_bijection E E' ->
  (A.wf_env E <-> B.wf_env E').
Proof.
  intuition eauto.
Qed.

(** We need a few corollaries of the substitution lemmas for
    the bijections. *)

Lemma typ_bijection_subst_head : forall E E' T1 T2 U1 U2 X,
  typ_bijection ([(X,Typ)] ++ E) T1 ([(X,Typ)] ++ E') T2 ->
  typ_bijection E U1 E' U2 ->
  typ_bijection E (A.subst_tt X U1 T1) E' (B.subst X U2 T2).
Proof.
  intros.
  rewrite_env (nil ++ E).
  rewrite_env (nil ++ E').
  apply typ_bijection_subst; simpl_env; auto.
Qed.

Lemma typ_bijection_subst_head_open : forall E E' T1 T2 U1 U2 X,
  X `notin` (A.fv_tt T1 `union` fv_spec Typ T2) ->
  typ_bijection ([(X,Typ)] ++ E) (A.open_tt T1 X) ([(X,Typ)] ++ E') (B.open T2 (B.typ_fvar X)) ->
  typ_bijection E U1 E' U2 ->
  typ_bijection E (A.open_tt T1 U1) E' (B.open T2 U2).
Proof with solve_lc_2; auto.
  intros.
  pose proof (typ_bijection_subst_head _ _ _ _ _ _ _ H0 H1).
  rewrite A'.subst_tt_open_tt in H2...
  rewrite B'.subst_open in H2...
  rewrite <- A'.subst_tt_fresh in H2...
  rewrite <- subst_tt_fresh in H2...
  simpl in H2.
  destruct (X == X); intuition.
Qed.

Lemma exp_bijection_subst_ee_head : forall E E' e1 e2 U1 U2 X,
  exp_bijection ([(X,Exp)] ++ E) e1 ([(X,Exp)] ++ E') e2 ->
  exp_bijection E U1 E' U2 ->
  exp_bijection E (A.subst_ee X U1 e1) E' (B.subst X U2 e2).
Proof.
  intros.
  rewrite_env (nil ++ E).
  rewrite_env (nil ++ E').
  apply exp_bijection_subst_ee; simpl_env; auto.
Qed.

Lemma exp_bijection_subst_ee_head_open : forall E E' e1 e2 U1 U2 X,
  X `notin` (A.fv_ee e1 `union` fv_spec Exp e2) ->
  exp_bijection ([(X,Exp)] ++ E) (A.open_ee e1 X) ([(X,Exp)] ++ E') (B.open e2 (B.exp_fvar X)) ->
  exp_bijection E U1 E' U2 ->
  exp_bijection E (A.open_ee e1 U1) E' (B.open e2 U2).
Proof with solve_lc_2; auto.
  intros.
  pose proof (exp_bijection_subst_ee_head _ _ _ _ _ _ _ H0 H1).
  rewrite A'.subst_ee_open_ee in H2...
  rewrite B'.subst_open in H2...
  rewrite <- A'.subst_ee_fresh in H2...
  rewrite <- subst_ee_fresh in H2...
  simpl in H2.
  destruct (X == X); intuition.
Qed.

Lemma exp_bijection_subst_te_head : forall E E' e1 e2 U1 U2 X,
  exp_bijection ([(X,Typ)] ++ E) e1 ([(X,Typ)] ++ E') e2 ->
  typ_bijection E U1 E' U2 ->
  exp_bijection E (A.subst_te X U1 e1) E' (B.subst X U2 e2).
Proof.
  intros.
  rewrite_env (nil ++ E).
  rewrite_env (nil ++ E').
  apply exp_bijection_subst_te; simpl_env; auto.
Qed.

Lemma exp_bijection_subst_te_head_open : forall E E' e1 e2 U1 U2 X,
  X `notin` (A.fv_te e1 `union` fv_spec Typ e2) ->
  exp_bijection ([(X,Typ)] ++ E) (A.open_te e1 X) ([(X,Typ)] ++ E') (B.open e2 (B.typ_fvar X)) ->
  typ_bijection E U1 E' U2 ->
  exp_bijection E (A.open_te e1 U1) E' (B.open e2 U2).
Proof with solve_lc_2; auto.
  intros.
  pose proof (exp_bijection_subst_te_head _ _ _ _ _ _ _ H0 H1).
  rewrite A'.subst_te_open_te in H2...
  rewrite B'.subst_open in H2...
  rewrite <- A'.subst_te_fresh in H2...
  rewrite <- subst_te_fresh in H2...
  simpl in H2.
  destruct (X == X); intuition.
Qed.

(** We now prove that the main Fsub relations derive the same sets of
    judgements. *)

Lemma sub_bijection_1 : forall E E' T T' S S',
  A.sub E S T ->
  env_bijection E E' ->
  typ_bijection (A.to_senv E) S (B.to_senv E') S' ->
  typ_bijection (A.to_senv E) T (B.to_senv E') T' ->
  B.sub E' S' T'.
Proof with simpl; simpl_env; eauto.
  intros E E' T T' S S' H.
  revert E' T' S'.
  induction H; intros F' T' S' J1 J2 J3.
  Case "sub_top".
    inversion J3; subst...
  Case "sub_refl_tvar".
    inversion J2; subst.
    inversion J3; subst...
  Case "sub_trans_tvar".
    inversion J2; subst.
    destruct (env_bijection_binds_sub_1 _ _ _ _ H J1) as [U' [? ?]].
    eapply B.sub_trans_tvar with (U := U')...
  Case "sub_arrow".
    inversion J2; subst.
    inversion J3; subst...
  Case "sub_all".
    inversion J2; subst.
    inversion J3; subst.
    pick fresh Y and apply B.sub_all...
    apply H1 with (X := Y)...
    simpl_env; constructor...
  Case "sub_sum".
    inversion J2; subst.
    inversion J3; subst...
Qed.

Hint Resolve sub_bijection_1.

Lemma sub_bijection_2 : forall E E' T T' S S',
  B.sub E' S' T' ->
  env_bijection E E' ->
  typ_bijection (A.to_senv E) S (B.to_senv E') S' ->
  typ_bijection (A.to_senv E) T (B.to_senv E') T' ->
  A.sub E S T.
Proof with simpl; simpl_env; eauto.
  intros E E' T T' S S' H.
  revert E T S.
  induction H; intros F' T' S' J1 J2 J3.
  Case "sub_top".
    inversion J3; subst...
  Case "sub_refl_tvar".
    inversion J2; subst.
    inversion J3; subst...
  Case "sub_trans_tvar".
    inversion J2; subst.
    destruct (env_bijection_binds_sub_2 _ _ _ _ H J1) as [U' [? ?]].
    eapply A.sub_trans_tvar with (U := U')...
  Case "sub_arrow".
    inversion J2; subst.
    inversion J3; subst...
  Case "sub_all".
    inversion J2; subst.
    inversion J3; subst.
    pick fresh Y and apply A.sub_all...
    apply H1 with (X := Y)...
    simpl_env; constructor...
  Case "sub_sum".
    inversion J2; subst.
    inversion J3; subst...
Qed.

Hint Resolve sub_bijection_2.

Lemma typing_bijection_1 : forall E E' e e' T T',
  A.typing E e T ->
  env_bijection E E' ->
  exp_bijection (A.to_senv E) e (B.to_senv E') e' ->
  typ_bijection (A.to_senv E) T (B.to_senv E') T' ->
  B.typing E' e' T'.
Proof with simplify_senv_bijection; simpl; simpl_env; eauto.
  intros E E' e e' T T' H.
  revert E' e' T'.
  induction H; intros F' f' T' J1 J2 J3.
  Case "typing_var".
    inversion J2; subst.
    destruct (env_bijection_binds_typ_1 _ _ _ _ H0 J1) as [U' [? ?]].
    assert (T' = U'). eapply typ_bijection_unique; eauto. subst.
    eauto.
  Case "typing_abs".
    inversion J2; subst.
    inversion J3; subst.
    assert (T'0 = T1'). eapply typ_bijection_unique; eauto. subst.
    pick fresh y and apply B.typing_abs.
    apply H0 with (x := y); auto.
      simpl_env; constructor...
      idtac...
      simpl_env. apply typ_bijection_weakening_head; auto.
        apply ok_push; eauto.
        apply ok_push; eauto.
  Case "typing_app".
    inversion J2; subst...
    destruct (typ_bijection_total (A.to_senv E) T1) as [E' [T1' [? ?]]].
      assert (Q : A.wf_typ (A.to_senv E) (A.typ_arrow T1 T2)).
        eapply proj2.
        eapply proj2.
        eapply A''.typing_regular...
      inversion Q; subst...
    assert (Q : senv_bijection (A.to_senv E) (B.to_senv F'))...
    eapply B.typing_app with (T1 := T1')...
      eapply IHtyping1... rewrite H6 in *...
      eapply IHtyping2... rewrite H6 in *...
  Case "typing_tabs".
    inversion J2; subst.
    inversion J3; subst.
    assert (T'0 = T1'). eapply typ_bijection_unique; eauto. subst.
    pick fresh Y and apply B.typing_tabs.
    apply H0 with (X := Y); auto.
      simpl_env; constructor...
      idtac...
      simpl_env.
      apply H9...
  Case "typing_tapp".
    inversion J2; subst...
    destruct (typ_bijection_total (A.to_senv E) (A.typ_all T1 T2))
          as [E' [T'' [K1 K2]]].
      eapply proj2.
      eapply proj2.
      eapply A''.typing_regular...
    inversion K1; subst.
    inversion K2; subst.
    assert (senv_bijection (A.to_senv E) (B.to_senv F'))...
    pick fresh X.
    lapply (H9 X); [ intros | auto ].
    assert (typ_bijection (A.to_senv E) (A.open_tt T2 T)
                          (A.to_senv E) (B.open T2' T'0)).
      apply typ_bijection_subst_head_open with (X := X); auto.
      rewrite H6 in *...
    assert (T' = B.open T2' T'0); subst.
      eapply typ_bijection_unique; eauto.
      rewrite H6 in *...
    eapply B.typing_tapp.
      apply IHtyping... rewrite H6 in *...
      eapply sub_bijection_1; eauto.
        rewrite H6 in *...
  Case "typing_sub".
    destruct (typ_bijection_total (A.to_senv E) S) as [E' [T1' [K1 K2]]].
      eapply proj1.
      eapply proj2.
      eapply A''.sub_regular...
    assert (senv_bijection (A.to_senv E) (B.to_senv F'))...
    apply B.typing_sub with (S := T1').
      apply IHtyping... rewrite H4 in *...
      eapply sub_bijection_1; eauto.
        rewrite H4 in *...
  Case "typing_let".
    inversion J2; subst.
    destruct (typ_bijection_total (A.to_senv E) T1) as [E' [T1' [K1 K2]]].
      eapply proj2.
      eapply proj2.
      eapply A''.typing_regular...
    assert (senv_bijection (A.to_senv E) (B.to_senv F'))...
    pick fresh x and apply B.typing_let.
      instantiate (1 := T1').
      apply IHtyping... rewrite H6 in *...
      apply H1 with (x := x); auto.
        simpl_env; constructor... rewrite H6 in *...
        idtac...
        simpl_env. apply typ_bijection_weakening_head; auto.
          apply ok_push...
          apply ok_push...
  Case "typing_inl".
    inversion J2; subst.
    inversion J3; subst...
  Case "typing_inr".
    inversion J2; subst.
    inversion J3; subst...
  Case "typing_case".
    inversion J2; subst.
    destruct (typ_bijection_total (A.to_senv E) T1) as [? [T1' [? ?]]].
      assert (Q : A.wf_typ (A.to_senv E) (A.typ_sum T1 T2)).
        eapply proj2.
        eapply proj2.
        eapply A''.typing_regular...
      inversion Q; subst...
    destruct (typ_bijection_total (A.to_senv E) T2) as [? [T2' [? ?]]].
      assert (Q : A.wf_typ (A.to_senv E) (A.typ_sum T1 T2)).
        eapply proj2.
        eapply proj2.
        eapply A''.typing_regular...
      inversion Q; subst...
    assert (senv_bijection (A.to_senv E) (B.to_senv F'))...
    pick fresh x and apply B.typing_case.
      instantiate (2 := T1'). instantiate (1 := T2').
      apply IHtyping... rewrite H14 in *...
      apply H1 with (x := x); auto.
        constructor... rewrite H14 in *...
        idtac...
        simpl; simpl_env. apply typ_bijection_weakening_head; auto.
          apply ok_push...
          apply ok_push...
      apply H3 with (x := x); auto.
        constructor... rewrite H14 in *...
        idtac...
        simpl; simpl_env. apply typ_bijection_weakening_head; auto.
          apply ok_push...
          apply ok_push...
Qed.

Lemma typing_bijection_2 : forall E E' e e' T T',
  B.typing E' e' T' ->
  env_bijection E E' ->
  exp_bijection (A.to_senv E) e (B.to_senv E') e' ->
  typ_bijection (A.to_senv E) T (B.to_senv E') T' ->
  A.typing E e T.
Proof with simplify_senv_bijection; simpl; simpl_env; eauto.
  intros E E' e e' T T' H.
  revert E e T.
  induction H; intros F' f' T' J1 J2 J3.
  Case "typing_var".
    inversion J2; subst.
    destruct (env_bijection_binds_typ_2 _ _ _ _ H0 J1) as [U' [? ?]].
    assert (T' = U'). eapply typ_bijection_injective; eauto. subst.
    eauto.
  Case "typing_abs".
    inversion J2; subst.
    inversion J3; subst.
    assert (T = T0). eapply typ_bijection_injective; eauto. subst.
    pick fresh y and apply A.typing_abs.
    apply H0 with (x := y); auto.
      simpl_env; constructor...
      idtac...
      simpl_env. apply typ_bijection_weakening_head; auto.
        apply ok_push; eauto.
        apply ok_push; eauto.
  Case "typing_app".
    inversion J2; subst...
    destruct (typ_bijection_surjective (B.to_senv E) T1) as [E' [T1' [? ?]]].
      assert (Q : B.wf_typ (B.to_senv E) (B.typ_arrow T1 T2)).
        eapply proj2.
        eapply proj2.
        eapply B''.typing_regular...
      inversion Q; subst...
    assert (Q : senv_bijection (A.to_senv F') (B.to_senv E))...
    eapply A.typing_app with (T1 := T1')...
      eapply IHtyping1... rewrite H5 in *...
      eapply IHtyping2... rewrite H5 in *...
  Case "typing_tabs".
    inversion J2; subst.
    inversion J3; subst.
    assert (T = T0). eapply typ_bijection_injective; eauto. subst.
    pick fresh Y and apply A.typing_tabs.
    apply H0 with (X := Y); auto.
      simpl_env; constructor...
      idtac...
      simpl_env. apply H9...
  Case "typing_tapp".
    inversion J2; subst...
    destruct (typ_bijection_surjective (B.to_senv E) (B.typ_all T1 T2))
          as [E' [T'' [K1 K2]]].
      eapply proj2.
      eapply proj2.
      eapply B''.typing_regular...
    inversion K1; subst.
    inversion K2; subst.
    assert (senv_bijection (A.to_senv F') (B.to_senv E))...
    pick fresh X.
    lapply (H9 X); [ intros | auto ].
    assert (typ_bijection (A.to_senv F') (A.open_tt T4 T0)
                          (A.to_senv F') (B.open T2 T)).
      apply typ_bijection_subst_head_open with (X := X); auto.
      rewrite H4 in *...
      rewrite H4 in *...
    assert (T' = A.open_tt T4 T0); subst.
      eapply typ_bijection_injective; eauto.
      rewrite H4 in *...
    eapply A.typing_tapp.
      apply IHtyping... rewrite H4 in *...
      eapply sub_bijection_2; eauto.
        rewrite H4 in *...
  Case "typing_sub".
    destruct (typ_bijection_surjective (B.to_senv E) S) as [E' [T1' [K1 K2]]].
      eapply proj1.
      eapply proj2.
      eapply B''.sub_regular...
    assert (senv_bijection (A.to_senv F') (B.to_senv E))...
    apply A.typing_sub with (S := T1').
      apply IHtyping... rewrite H4 in *...
      eapply sub_bijection_2; eauto.
        rewrite H4 in *...
  Case "typing_let".
    inversion J2; subst.
    destruct (typ_bijection_surjective (B.to_senv E) T1) as [E' [T1' [? ?]]].
      eapply proj2.
      eapply proj2.
      eapply B''.typing_regular...
    assert (senv_bijection (A.to_senv F') (B.to_senv E))...
    pick fresh x and apply A.typing_let.
      instantiate (1 := T1').
      apply IHtyping... rewrite H9 in *...
      apply H1 with (x := x); auto.
        simpl_env; constructor... rewrite H9 in *...
        idtac...
        simpl_env. apply typ_bijection_weakening_head; auto.
          apply ok_push...
          apply ok_push...
  Case "typing_inl".
    inversion J2; subst.
    inversion J3; subst...
  Case "typing_inr".
    inversion J2; subst.
    inversion J3; subst...
  Case "typing_case".
    inversion J2; subst.
    destruct (typ_bijection_surjective (B.to_senv E) T1) as [? [T1' [? ?]]].
      assert (Q : B.wf_typ (B.to_senv E) (B.typ_sum T1 T2)).
        eapply proj2.
        eapply proj2.
        eapply B''.typing_regular...
      inversion Q; subst...
    destruct (typ_bijection_surjective (B.to_senv E) T2) as [? [T2' [? ?]]].
      assert (Q : B.wf_typ (B.to_senv E) (B.typ_sum T1 T2)).
        eapply proj2.
        eapply proj2.
        eapply B''.typing_regular...
      inversion Q; subst...
    assert (senv_bijection (A.to_senv F') (B.to_senv E))...
    pick fresh x and apply A.typing_case.
      instantiate (2 := T1'). instantiate (1 := T2').
      apply IHtyping... rewrite H14 in *...
      apply H1 with (x := x); auto.
        constructor... rewrite H14 in *...
        idtac...
        simpl; simpl_env. apply typ_bijection_weakening_head; auto.
          apply ok_push...
          apply ok_push...
      apply H3 with (x := x); auto.
        constructor... rewrite H14 in *...
        idtac...
        simpl; simpl_env. apply typ_bijection_weakening_head; auto.
          apply ok_push...
          apply ok_push...
Qed.

Lemma value_bijection_1 : forall E E' e e',
  A.value e ->
  exp_bijection E e E' e' ->
  B.value e'.
Proof.
  intros E E' e e' H.
  revert E E' e'.
  induction H; intros F F' e' J; inversion J; subst.
  eapply B.value_abs; eauto.
  eapply B.value_tabs; eauto.
  eapply B.value_inl; intuition eauto.
  eapply B.value_inr; intuition eauto.
Qed.

Hint Resolve value_bijection_1.

Lemma value_bijection_2 : forall E E' e e',
  B.value e' ->
  exp_bijection E e E' e' ->
  A.value e.
Proof.
  intros E E' e e' H.
  revert E E' e.
  induction H; intros F F' e J; inversion J; subst.
  eapply A.value_abs; eauto.
  eapply A.value_tabs; eauto.
  eapply A.value_inl; intuition eauto.
  eapply A.value_inr; intuition eauto.
Qed.

Hint Resolve value_bijection_2.

Lemma red_bijection_1 : forall E E' e1 e1' e2 e2',
  A.red e1 e2 ->
  exp_bijection E e1 E' e1' ->
  exp_bijection E e2 E' e2' ->
  B.red e1' e2'.
Proof with simplify_senv_bijection; solve_lc_2; eauto.
  intros E E' e1 e1' e2 e2' H.
  revert E E' e1' e2'.
  induction H; intros F F' f1' f2' J1 J2.
  Case "red_app_1".
    inversion J1; subst.
    inversion J2; subst.
    assert (e2' = e2'0). eapply exp_bijection_unique... subst.
    eapply B.red_app_1...
  Case "red_app_2".
    inversion J1; subst.
    inversion J2; subst.
    assert (e1' = e1'0). eapply exp_bijection_unique... subst.
    eapply B.red_app_2...
  Case "red_tapp".
    inversion J1; subst.
    inversion J2; subst.
    assert (T' = T'0). eapply typ_bijection_unique... subst.
    eapply B.red_tapp...
  Case "red_abs".
    inversion J1; subst.
    inversion H4; subst.
    pick fresh x.
    lapply (H9 x); [ intros Q | auto ].
    assert (exp_bijection F (A.open_ee e1 v2) F' (B.open e' e2')).
      apply exp_bijection_subst_ee_head_open with (X := x); auto.
    assert (f2' = B.open e' e2'); subst.
      eauto using exp_bijection_unique.
    eapply B.red_abs...
  Case "red_tabs".
    inversion J1; subst.
    inversion H3; subst.
    pick fresh X.
    lapply (H8 X); [ intros Q | auto ].
    assert (exp_bijection F (A.open_te e1 T2) F' (B.open e'0 T')).
      apply exp_bijection_subst_te_head_open with (X := X); auto.
    assert (f2' = B.open e'0 T'); subst.
      eauto using exp_bijection_unique.
    eapply B.red_tabs...
  Case "red_let_1".
    inversion J1; subst.
    inversion J2; subst.
    assert (e2' = e2'0); subst.
      pick fresh x.
      lapply (H7 x); [ intros | auto ].
      lapply (H9 x); [ intros | auto ].
      assert (B.open e2' (B.exp_fvar x) = B.open e2'0 (B.exp_fvar x)).
        eapply exp_bijection_unique...
      eapply open_injective with (X := x)...
    eapply B.red_let_1...
  Case "red_let".
    inversion J1; subst.
    pick fresh x.
    lapply (H7 x); [ intros Q | auto ].
    assert (exp_bijection F (A.open_ee e2 v1) F' (B.open e2' e1')).
      apply exp_bijection_subst_ee_head_open with (X := x); auto.
    assert (f2' = B.open e2' e1'); subst.
      eauto using exp_bijection_unique.
    eapply B.red_let...
  Case "red_inl_1".
    inversion J1; subst.
    inversion J2; subst.
    eauto.
  Case "red_inr_1".
    inversion J1; subst.
    inversion J2; subst.
    eauto.
  Case "red_case_1".
    inversion J1; subst.
    inversion J2; subst.
    assert (e2' = e2'0); subst.
      pick fresh x.
      lapply (H8 x); [ intros | auto ].
      lapply (H11 x); [ intros | auto ].
      assert (B.open e2' (B.exp_fvar x) = B.open e2'0 (B.exp_fvar x)).
        eapply exp_bijection_unique...
      eapply open_injective with (X := x)...
    assert (e3' = e3'0); subst.
      pick fresh x.
      lapply (H9 x); [ intros | auto ].
      lapply (H12 x); [ intros | auto ].
      assert (B.open e3' (B.exp_fvar x) = B.open e3'0 (B.exp_fvar x)).
        eapply exp_bijection_unique...
      eapply open_injective with (X := x)...
    eauto.
  Case "red_case_inl".
    inversion J1; subst.
    inversion H5; subst.
    pick fresh x.
    lapply (H8 x); [ intros Q | auto ].
    assert (exp_bijection F (A.open_ee e2 v1) F' (B.open e2' e')).
      apply exp_bijection_subst_ee_head_open with (X := x); auto.
    assert (f2' = B.open e2' e'); subst.
      eauto using exp_bijection_unique.
    eapply B.red_case_inl...
  Case "red_case_inr".
    inversion J1; subst.
    inversion H5; subst.
    pick fresh x.
    lapply (H8 x); [ intros Q | auto ].
    assert (exp_bijection F (A.open_ee e3 v1) F' (B.open e3' e')).
      apply exp_bijection_subst_ee_head_open with (X := x); auto.
    assert (f2' = B.open e3' e'); subst.
      eauto using exp_bijection_unique.
    eapply B.red_case_inr...
Qed.

Lemma red_bijection_2 : forall E E' e1 e1' e2 e2',
  B.red e1' e2' ->
  exp_bijection E e1 E' e1' ->
  exp_bijection E e2 E' e2' ->
  A.red e1 e2.
Proof with simplify_senv_bijection; solve_lc_2; eauto.
  intros E E' e1 e1' e2 e2' H.
  revert E E' e1 e2.
  induction H; intros F F' f1' f2' J1 J2.
  Case "red_app_1".
    inversion J1; subst.
    inversion J2; subst.
    assert (e3 = e5). eapply exp_bijection_injective... subst.
    eapply A.red_app_1...
  Case "red_app_2".
    inversion J1; subst.
    inversion J2; subst.
    assert (e0 = e4). eapply exp_bijection_injective... subst.
    eapply A.red_app_2...
  Case "red_tapp".
    inversion J1; subst.
    inversion J2; subst.
    assert (T = T0). eapply typ_bijection_injective... subst.
    eapply A.red_tapp...
  Case "red_abs".
    inversion J1; subst.
    inversion H6; subst.
    pick fresh x.
    lapply (H9 x); [ intros Q | auto ].
    assert (exp_bijection F (A.open_ee e e2) F' (B.open e1 v2)).
      apply exp_bijection_subst_ee_head_open with (X := x); auto.
    assert (f2' = A.open_ee e e2); subst.
      eauto using exp_bijection_injective.
    eapply A.red_abs...
  Case "red_tabs".
    inversion J1; subst.
    inversion H5; subst.
    pick fresh X.
    lapply (H8 X); [ intros Q | auto ].
    assert (exp_bijection F (A.open_te e0 T) F' (B.open e1 T2)).
      apply exp_bijection_subst_te_head_open with (X := X); auto.
    assert (f2' = A.open_te e0 T); subst.
      eauto using exp_bijection_injective.
    eapply A.red_tabs...
  Case "red_let_1".
    inversion J1; subst.
    inversion J2; subst.
    assert (e3 = e5); subst.
      pick fresh x.
      lapply (H7 x); [ intros | auto ].
      lapply (H9 x); [ intros | auto ].
      assert (A.open_ee e3 x = A.open_ee e5 x).
        eapply exp_bijection_injective...
      apply open_ee_injective with (X := x)...
    eapply A.red_let_1...
  Case "red_let".
    inversion J1; subst.
    pick fresh x.
    lapply (H7 x); [ intros Q | auto ].
    assert (exp_bijection F (A.open_ee e0 e1) F' (B.open e2 v1)).
      apply exp_bijection_subst_ee_head_open with (X := x); auto.
    assert (f2' = A.open_ee e0 e1); subst.
      eauto using exp_bijection_injective.
    eapply A.red_let...
  Case "red_inl_1".
    inversion J1; subst.
    inversion J2; subst.
    eauto.
  Case "red_inr_1".
    inversion J1; subst.
    inversion J2; subst.
    eauto.
  Case "red_case_1".
    inversion J1; subst.
    inversion J2; subst.
    assert (e4 = e7); subst.
      pick fresh x.
      lapply (H8 x); [ intros | auto ].
      lapply (H11 x); [ intros | auto ].
      assert (A.open_ee e4 x = A.open_ee e7 x).
        eapply exp_bijection_injective...
      apply open_ee_injective with (X := x)...
    assert (e5 = e8); subst.
      pick fresh x.
      lapply (H9 x); [ intros | auto ].
      lapply (H12 x); [ intros | auto ].
      assert (A.open_ee e5 x = A.open_ee e8 x).
        eapply exp_bijection_injective...
      apply open_ee_injective with (X := x)...
    eauto.
  Case "red_case_inl".
    inversion J1; subst.
    inversion H7; subst.
    pick fresh x.
    lapply (H8 x); [ intros Q | auto ].
    assert (exp_bijection F (A.open_ee e0 e) F' (B.open e2 v1)).
      apply exp_bijection_subst_ee_head_open with (X := x); auto.
    assert (f2' = A.open_ee e0 e); subst.
      eauto using exp_bijection_injective.
    eapply A.red_case_inl...
  Case "red_case_inr".
    inversion J1; subst.
    inversion H7; subst.
    pick fresh x.
    lapply (H9 x); [ intros Q | auto ].
    assert (exp_bijection F (A.open_ee e4 e) F' (B.open e3 v1)).
      apply exp_bijection_subst_ee_head_open with (X := x); auto.
    assert (f2' = A.open_ee e4 e); subst.
      eauto using exp_bijection_injective.
    eapply A.red_case_inr...
Qed.
