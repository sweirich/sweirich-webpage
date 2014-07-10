(** Definition of Fsub (System F with subtyping).

    We represent syntax with an encoding into the lambda calculus.

    NOTE: We define a number of [Notation]s which are used only for
    parsing, since the code here is directly copied from another
    development.  The notations help smooth over trivial differences
    in the names of lemmas and functions. *)


Require Export Metatheory.
Require Export Lib_Typed_Lambda.
Require Export Common.


(* ********************************************************************** *)
(** * Pre-terms *)

Module Export Const <: CONST.

Inductive syntax_c : Set :=
| typ_top_c   : syntax_c
| typ_arrow_c : syntax_c
| typ_all_c   : syntax_c
| typ_sum_c   : syntax_c
| exp_abs_c   : syntax_c
| exp_app_c   : syntax_c
| exp_tabs_c  : syntax_c
| exp_tapp_c  : syntax_c
| exp_let_c   : syntax_c
| exp_inl_c   : syntax_c
| exp_inr_c   : syntax_c
| exp_case_c  : syntax_c.

Definition const := syntax_c.
Definition base_sort := tag.

Lemma eq_base_sort_dec : forall (x y : base_sort), {x = y} + {x <> y}.
Proof.
  decide equality.
Qed.

Notation Typ := (lt_base Typ).
Notation Exp := (lt_base Exp).
Notation sort := (lambda_sort base_sort).

Definition signature (c : const) : sort :=
  match c with
    | typ_top_c => Typ
    | typ_arrow_c => lt_arrow Typ (lt_arrow Typ Typ)
    | typ_all_c => lt_arrow Typ (lt_arrow (lt_arrow Typ Typ) Typ)
    | typ_sum_c => lt_arrow Typ (lt_arrow Typ Typ)
    | exp_abs_c => lt_arrow Typ (lt_arrow (lt_arrow Exp Exp) Exp)
    | exp_app_c => lt_arrow Exp (lt_arrow Exp Exp)
    | exp_tabs_c => lt_arrow Typ (lt_arrow (lt_arrow Typ Exp) Exp)
    | exp_tapp_c => lt_arrow Exp (lt_arrow Typ Exp)
    | exp_let_c => lt_arrow Exp (lt_arrow (lt_arrow Exp Exp) Exp)
    | exp_inl_c => lt_arrow Exp Exp
    | exp_inr_c => lt_arrow Exp Exp
    | exp_case_c => lt_arrow Exp (lt_arrow (lt_arrow Exp Exp)
                                 (lt_arrow (lt_arrow Exp Exp) Exp))
  end.

End Const.

Module Export L := Lam Const.


(* ********************************************************************** *)
(** * Notations *)

(** NOTE: The block of notations below is purely to smooth over
    differences stemming from the fact that much of the code in this
    development is copied directly from another Fsub development. *)

Notation exp := syntax (only parsing).
Notation typ := syntax (only parsing).

Notation fv_tt := fv (only parsing).

Notation open_tt := open (only parsing).
Notation open_te := open (only parsing).
Notation open_ee := open (only parsing).

Notation subst_tt := subst (only parsing).
Notation subst_te := subst (only parsing).
Notation subst_ee := subst (only parsing).

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

(** NOTE: The block of notations below is needed to provide a
    reasonable way of writing terms. *)

Notation "r @ s" := (app r s) (at level 40, left associativity).

Notation typ_fvar := fvar.
Notation exp_fvar := fvar.

Notation typ_top :=
  (const typ_top_c).
Notation "'typ_arrow' s1"       :=
  (app (const typ_arrow_c @ s1)) (at level 2).
Notation "'typ_all' s1 'in' s2" :=
  (const typ_all_c @ s1 @ (abs Typ s2)) (at level 2).
Notation "'typ_sum' s1"         :=
  (app (const typ_sum_c @ s1 )) (at level 2).
Notation "'exp_abs' s1 'in' s2" :=
  (const exp_abs_c @ s1 @ (abs Exp s2)) (at level 2).
Notation "'exp_app' s1"         :=
  (app (const exp_app_c @ s1 )) (at level 2).
Notation "'exp_tabs' s1 'in' s2":=
  (const exp_tabs_c @ s1 @ (abs Typ s2)) (at level 2).
Notation "'exp_tapp' s1"        :=
  (app (const exp_tapp_c @ s1 )) (at level 2).
Notation "'exp_let' s1 'in' s2" :=
  (const exp_let_c @ s1 @ (abs Exp s2)) (at level 2).
Notation "'exp_inl' s1"         :=
  (const exp_inl_c @ s1) (at level 2).
Notation "'exp_inr' s1"         :=
  (const exp_inr_c @ s1) (at level 2).
Notation "'exp_case' s1 'left' s2 'right' s3" :=
  (const exp_case_c @ s1 @ (abs Exp s2) @ (abs Exp s3)) (at level 2).


(* ********************************************************************** *)
(** * #<a name="env"></a># Environments *)

Inductive binding : Set :=
  | bind_sub : typ -> binding
  | bind_typ : typ -> binding.

Notation env := (list (atom * binding)).
Notation empty := (@nil (atom * binding)).

Notation "[ x ]" := (x :: nil).

Definition subst_tb (Z : atom) (P : typ) (b : binding) : binding :=
  match b with
    | bind_sub T => bind_sub (subst_tt Z P T)
    | bind_typ T => bind_typ (subst_tt Z P T)
  end.

Notation senv := (list (atom * sort)).

Definition to_tag (b : binding) : sort :=
  match b with
    | bind_sub _ => Typ
    | bind_typ _ => Exp
  end.

Notation to_senv := (map to_tag).


(* ********************************************************************** *)
(** * #<a name="wf"></a># Well-formedness *)

Definition wf_typ E T := lc E T Typ.
Definition wf_exp E e := lc E e Exp.

Inductive wf_env : env -> Prop :=
  | wf_env_empty :
      wf_env empty
  | wf_env_sub : forall (E : env) (X : atom) (T : typ),
      wf_env E ->
      wf_typ (to_senv E) T ->
      X `notin` dom E ->
      wf_env ([(X, bind_sub T)] ++ E)
  | wf_env_typ : forall (E : env) (x : atom) (T : typ),
      wf_env E ->
      wf_typ (to_senv E) T ->
      x `notin` dom E ->
      wf_env ([(x, bind_typ T)] ++ E)
.


(* ********************************************************************** *)
(** * #<a name="sub"></a># Subtyping *)

Inductive sub : env -> typ -> typ -> Prop :=
  | sub_top : forall E S,
      wf_env E ->
      wf_typ (to_senv E) S ->
      sub E S typ_top
  | sub_refl_tvar : forall E X,
      wf_env E ->
      wf_typ (to_senv E) (typ_fvar X) ->
      sub E (typ_fvar X) (typ_fvar X)
  | sub_trans_tvar : forall U E T X,
      binds X (bind_sub U) E ->
      sub E U T ->
      sub E (typ_fvar X) T
  | sub_arrow : forall E S1 S2 T1 T2,
      sub E T1 S1 ->
      sub E S2 T2 ->
      sub E (typ_arrow S1 S2) (typ_arrow T1 T2)
  | sub_all : forall L E S1 S2 T1 T2,
      sub E T1 S1 ->
      (forall X : atom, X `notin` L ->
          sub ([(X, bind_sub T1)] ++ E) (open_tt S2 X) (open_tt T2 X)) ->
      sub E (typ_all S1 in S2) (typ_all T1 in T2)
  | sub_sum : forall E S1 S2 T1 T2,
      sub E S1 T1 ->
      sub E S2 T2 ->
      sub E (typ_sum S1 S2) (typ_sum T1 T2)
.


(* ********************************************************************** *)
(** * #<a name="typing_doc"></a># Typing *)

Inductive typing : env -> exp -> typ -> Prop :=
  | typing_var : forall E x T,
      wf_env E ->
      binds x (bind_typ T) E ->
      typing E (exp_fvar x) T
  | typing_abs : forall L E V e1 T1,
      (forall x : atom, x `notin` L ->
        typing ([(x, bind_typ V)] ++ E) (open_ee e1 x) T1) ->
      typing E (exp_abs V in e1) (typ_arrow V T1)
  | typing_app : forall T1 E e1 e2 T2,
      typing E e1 (typ_arrow T1 T2) ->
      typing E e2 T1 ->
      typing E (exp_app e1 e2) T2
  | typing_tabs : forall L E V e1 T1,
      (forall X : atom, X `notin` L ->
        typing ([(X, bind_sub V)] ++ E) (open_te e1 X) (open_tt T1 X)) ->
      typing E (exp_tabs V in e1) (typ_all V in T1)
  | typing_tapp : forall T1 E e1 T T2,
      typing E e1 (typ_all T1 in T2) ->
      sub E T T1 ->
      typing E (exp_tapp e1 T) (open_tt T2 T)
  | typing_sub : forall S E e T,
      typing E e S ->
      sub E S T ->
      typing E e T
  | typing_let : forall L T1 T2 e1 e2 E,
      typing E e1 T1 ->
      (forall x, x `notin` L ->
        typing ([(x, bind_typ T1)] ++ E) (open_ee e2 x) T2) ->
      typing E (exp_let e1 in e2) T2
  | typing_inl : forall T1 T2 e1 E,
      typing E e1 T1 ->
      wf_typ (to_senv E) T2 ->
      typing E (exp_inl e1) (typ_sum T1 T2)
  | typing_inr : forall T1 T2 e1 E,
      typing E e1 T2 ->
      wf_typ (to_senv E) T1 ->
      typing E (exp_inr e1) (typ_sum T1 T2)
  | typing_case : forall L T1 T2 T e1 e2 e3 E,
      typing E e1 (typ_sum T1 T2) ->
      (forall x : atom, x `notin` L ->
        typing ([(x, bind_typ T1)] ++ E) (open_ee e2 x) T) ->
      (forall x : atom, x `notin` L ->
        typing ([(x, bind_typ T2)] ++ E) (open_ee e3 x) T) ->
      typing E (exp_case e1 left e2 right e3) T
.


(* ********************************************************************** *)
(** * #<a name="values"></a># Values *)

Inductive value : exp -> Prop :=
  | value_abs : forall E T e1,
      wf_exp E (exp_abs T in e1) ->
      value (exp_abs T in e1)
  | value_tabs : forall E T e1,
      wf_exp E (exp_tabs T in e1) ->
      value (exp_tabs T in e1)
  | value_inl : forall e1,
      value e1 ->
      value (exp_inl e1)
  | value_inr : forall e1,
      value e1 ->
      value (exp_inr e1)
.


(* ********************************************************************** *)
(** * #<a name="reduction"></a># Reduction *)

Inductive red : exp -> exp -> Prop :=
  | red_app_1 : forall E e1 e1' e2,
      wf_exp E (exp_app e1 e2) ->
      red e1 e1' ->
      red (exp_app e1 e2) (exp_app e1' e2)
  | red_app_2 : forall E e1 e2 e2',
      wf_exp E (exp_app e1 e2) ->
      value e1 ->
      red e2 e2' ->
      red (exp_app e1 e2) (exp_app e1 e2')
  | red_tapp : forall E e1 e1' V,
      wf_exp E (exp_tapp e1 V) ->
      red e1 e1' ->
      red (exp_tapp e1 V) (exp_tapp e1' V)
  | red_abs : forall E T e1 v2,
      wf_exp E (exp_app (exp_abs T in e1) v2) ->
      value v2 ->
      red (exp_app (exp_abs T in e1) v2) (open_ee e1 v2)
  | red_tabs : forall E T1 e1 T2,
      wf_exp E (exp_tapp (exp_tabs T1 in e1) T2) ->
      red (exp_tapp (exp_tabs T1 in e1) T2) (open_te e1 T2)
  | red_let_1 : forall E e1 e1' e2,
      wf_exp E (exp_let e1 in e2) ->
      red e1 e1' ->
      red (exp_let e1 in e2) (exp_let e1' in e2)
  | red_let : forall E v1 e2,
      wf_exp E (exp_let v1 in e2) ->
      value v1 ->
      red (exp_let v1 in e2) (open_ee e2 v1)
  | red_inl_1 : forall e1 e1',
      red e1 e1' ->
      red (exp_inl e1) (exp_inl e1')
  | red_inr_1 : forall e1 e1',
      red e1 e1' ->
      red (exp_inr e1) (exp_inr e1')
  | red_case_1 : forall E e1 e1' e2 e3,
      wf_exp E (exp_case e1 left e2 right e3) ->
      red e1 e1' ->
      red (exp_case e1 left e2 right e3) (exp_case e1' left e2 right e3)
  | red_case_inl : forall E v1 e2 e3,
      wf_exp E (exp_case (exp_inl v1) left e2 right e3)  ->
      value v1 ->
      red (exp_case (exp_inl v1) left e2 right e3) (open_ee e2 v1)
  | red_case_inr : forall E v1 e2 e3,
      wf_exp E (exp_case (exp_inr v1) left e2 right e3)  ->
      value v1 ->
      red (exp_case (exp_inr v1) left e2 right e3) (open_ee e3 v1)
.


(* ********************************************************************** *)
(** * Automation *)

Hint Constructors wf_env value red.
Hint Resolve sub_top sub_refl_tvar sub_arrow.
Hint Resolve sub_sum typing_inl typing_inr.
Hint Resolve typing_var typing_app typing_tapp typing_sub.
Hint Resolve typing_inl typing_inr.

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


(* ********************************************************************** *)
(** * #<a name="pick_fresh"></a># The "[pick fresh]" tactic *)

Ltac gather_atoms :=
  let A := gather_atoms_with (fun x : atoms => x) in
  let B := gather_atoms_with (fun x : atom => singleton x) in
  let C := gather_atoms_with (fun x : syntax => fv x) in
  let F := gather_atoms_with (fun x : env => dom x) in
  let G := gather_atoms_with (fun x : senv => dom x) in
  constr:(A `union` B `union` C `union` F `union` G).

Tactic Notation "pick" "fresh" ident(x) :=
  let L := gather_atoms in (pick fresh x for L).

Tactic Notation
      "pick" "fresh" ident(atom_name) "and" "apply" constr(lemma) :=
  let L := gather_atoms in
  pick fresh atom_name excluding L and apply lemma.
