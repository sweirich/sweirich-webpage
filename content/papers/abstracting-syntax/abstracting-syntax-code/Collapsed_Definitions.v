(** Definition of Fsub (System F with subtyping).

    We collapse the syntax of types of expressions into one inductive
    datatype.  We retain only one constructor each for bound and free
    variables.

    NOTE: We define a number of [Notation]s which are used only for
    parsing, since the code here is directly copied from another
    development.  The notations help smooth over trivial differences
    in the names of lemmas and functions. *)

Require Export Metatheory.
Require Export Common.


(* ********************************************************************** *)
(** * #<a name="syntax"></a># Syntax (pre-terms) *)

Inductive syntax : Set :=
  | bvar : nat -> syntax
  | fvar : atom -> syntax
  | typ_top : syntax
  | typ_arrow : syntax -> syntax -> syntax
  | typ_all : syntax -> syntax -> syntax
  | typ_sum : syntax -> syntax -> syntax
  | exp_abs : syntax -> syntax -> syntax
  | exp_app : syntax -> syntax -> syntax
  | exp_tabs : syntax -> syntax -> syntax
  | exp_tapp : syntax -> syntax -> syntax
  | exp_let : syntax -> syntax -> syntax
  | exp_inl : syntax -> syntax
  | exp_inr : syntax -> syntax
  | exp_case : syntax -> syntax -> syntax -> syntax
.

Coercion bvar : nat >-> syntax.
Coercion fvar : atom >-> syntax.

Notation typ_bvar := bvar (only parsing).
Notation typ_fvar := fvar (only parsing).
Notation exp_bvar := bvar (only parsing).
Notation exp_fvar := fvar (only parsing).

Notation typ := syntax (only parsing).
Notation exp := syntax (only parsing).


(* ********************************************************************** *)
(** * #<a name="open"></a># Opening terms *)

Fixpoint open_rec (K : nat) (U : syntax) (T : syntax)  {struct T} : syntax :=
  match T with
  | bvar J => if K === J then U else (bvar J)
  | fvar X => fvar X
  | typ_top => typ_top
  | typ_arrow T1 T2 => typ_arrow (open_rec K U T1) (open_rec K U T2)
  | typ_all T1 T2 => typ_all (open_rec K U T1) (open_rec (S K) U T2)
  | typ_sum T1 T2 => typ_sum (open_rec K U T1) (open_rec K U T2)
  | exp_abs V e1 => exp_abs  (open_rec K U V)  (open_rec (S K) U e1)
  | exp_app e1 e2 => exp_app  (open_rec K U e1) (open_rec K U e2)
  | exp_tabs V e1 => exp_tabs (open_rec K U V)  (open_rec (S K) U e1)
  | exp_tapp e1 V => exp_tapp (open_rec K U e1) (open_rec K U V)
  | exp_let e1 e2 => exp_let (open_rec K U e1) (open_rec (S K) U e2)
  | exp_inl e1 => exp_inl (open_rec K U e1)
  | exp_inr e2 => exp_inr (open_rec K U e2)
  | exp_case e1 e2 e3 =>
      exp_case (open_rec K U e1) (open_rec (S K) U e2) (open_rec (S K) U e3)
  end.

Definition open T U := open_rec 0 U T.

Notation open_tt := open (only parsing).
Notation open_te := open (only parsing).
Notation open_ee := open (only parsing).


(* ********************************************************************** *)
(** * #<a name="fv"></a># Free variables *)

Fixpoint fv (T : syntax) {struct T} : atoms :=
  match T with
  | bvar J => {}
  | fvar X => singleton X
  | typ_top => {}
  | typ_arrow T1 T2 => (fv T1) `union` (fv T2)
  | typ_all T1 T2 => (fv T1) `union` (fv T2)
  | typ_sum T1 T2 => (fv T1) `union` (fv T2)
  | exp_abs V e1 => (fv V) `union` (fv e1)
  | exp_app e1 e2 => (fv e1) `union` (fv e2)
  | exp_tabs V e1 => (fv V) `union` (fv e1)
  | exp_tapp e1 V => (fv V) `union` (fv e1)
  | exp_let e1 e2 => (fv e1) `union` (fv e2)
  | exp_inl e1 => (fv e1)
  | exp_inr e1 => (fv e1)
  | exp_case e1 e2 e3 => (fv e1) `union` (fv e2) `union` (fv e3)
  end.

Notation fv_tt := fv (only parsing).
Notation fv_te := fv (only parsing).
Notation fv_ee := fv (only parsing).


(* ********************************************************************** *)
(** * #<a name="subst"></a># Substitution *)

Fixpoint subst (Z : atom) (U : typ) (T : typ) {struct T} : typ :=
  match T with
  | bvar J => bvar J
  | fvar X => if X == Z then U else T
  | typ_top => typ_top
  | typ_arrow T1 T2 => typ_arrow (subst Z U T1) (subst Z U T2)
  | typ_all T1 T2  => typ_all (subst Z U T1) (subst Z U T2)
  | typ_sum T1 T2 => typ_sum (subst Z U T1) (subst Z U T2)
  | exp_abs V e1 => exp_abs  (subst Z U V)  (subst Z U e1)
  | exp_app e1 e2 => exp_app  (subst Z U e1) (subst Z U e2)
  | exp_tabs V e1 => exp_tabs (subst Z U V)  (subst Z U e1)
  | exp_tapp e1 V => exp_tapp (subst Z U e1) (subst Z U V)
  | exp_let e1 e2 => exp_let (subst Z U e1) (subst Z U e2)
  | exp_inl e1 => exp_inl (subst Z U e1)
  | exp_inr e1 => exp_inr (subst Z U e1)
  | exp_case e1 e2 e3 =>
      exp_case (subst Z U e1) (subst Z U e2) (subst Z U e3)
  end.

Notation subst_tt := subst (only parsing).
Notation subst_te := subst (only parsing).
Notation subst_ee := subst (only parsing).


(* ********************************************************************** *)
(** * #<a name="lc"></a># Local closure *)

Inductive lc : syntax -> Prop :=
  | lc_var : forall X,
      lc (fvar X)
  | type_top :
      lc typ_top
  | type_arrow : forall T1 T2,
      lc T1 ->
      lc T2 ->
      lc (typ_arrow T1 T2)
  | type_all : forall L T1 T2,
      lc T1 ->
      (forall X : atom, X `notin` L -> lc (open T2 X)) ->
      lc (typ_all T1 T2)
  | type_sum : forall T1 T2,
      lc T1 ->
      lc T2 ->
      lc (typ_sum T1 T2)
  | expr_abs : forall L T e1,
      lc T ->
      (forall x : atom, x `notin` L -> lc (open e1 x)) ->
      lc (exp_abs T e1)
  | expr_app : forall e1 e2,
      lc e1 ->
      lc e2 ->
      lc (exp_app e1 e2)
  | expr_tabs : forall L T e1,
      lc T ->
      (forall X : atom, X `notin` L -> lc (open e1 X)) ->
      lc (exp_tabs T e1)
  | expr_tapp : forall e1 V,
      lc e1 ->
      lc V ->
      lc (exp_tapp e1 V)
  | expr_let : forall L e1 e2,
      lc e1 ->
      (forall x : atom, x `notin` L -> lc (open e2 x)) ->
      lc (exp_let e1 e2)
  | expr_inl : forall e1,
      lc e1 ->
      lc (exp_inl e1)
  | expr_inr : forall e1,
      lc e1 ->
      lc (exp_inr e1)
  | expr_case : forall L e1 e2 e3,
      lc e1 ->
      (forall x : atom, x `notin` L -> lc (open e2 x)) ->
      (forall x : atom, x `notin` L -> lc (open e3 x)) ->
      lc (exp_case e1 e2 e3).

Notation type := lc (only parsing).
Notation expr := lc (only parsing).


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

Notation senv := (list (atom * tag)).

Definition to_tag (b : binding) : tag :=
  match b with
    | bind_sub _ => Typ
    | bind_typ _ => Exp
  end.

Notation to_senv := (map to_tag).


(* ********************************************************************** *)
(** * #<a name="wf"></a># Well-formedness *)

Inductive wf_typ : senv -> typ -> Prop :=
  | wf_typ_top : forall E,
      ok E ->
      wf_typ E typ_top
  | wf_typ_var : forall E (X : atom),
      ok E ->
      binds X Typ E ->
      wf_typ E (typ_fvar X)
  | wf_typ_arrow : forall E T1 T2,
      wf_typ E T1 ->
      wf_typ E T2 ->
      wf_typ E (typ_arrow T1 T2)
  | wf_typ_all : forall L E T1 T2,
      wf_typ E T1 ->
      (forall X : atom, X `notin` L ->
        wf_typ ([(X, Typ)] ++ E) (open_tt T2 X)) ->
      wf_typ E (typ_all T1 T2)
  | wf_typ_sum : forall E T1 T2,
      wf_typ E T1 ->
      wf_typ E T2 ->
      wf_typ E (typ_sum T1 T2)
.

Inductive wf_exp : senv -> exp -> Prop :=
  | wf_exp_var : forall E (x : atom),
      ok E ->
      binds x Exp E->
      wf_exp E (exp_fvar x)
  | wf_exp_abs : forall L E T e,
      wf_typ E T ->
      (forall x : atom, x `notin` L ->
        wf_exp ([(x,Exp)] ++ E) (open_ee e x)) ->
      wf_exp E (exp_abs T e)
  | wf_exp_app : forall E e1 e2,
      wf_exp E e1 ->
      wf_exp E e2 ->
      wf_exp E (exp_app e1 e2)
  | wf_exp_tabs : forall L E T e,
      wf_typ E T ->
      (forall X : atom, X `notin` L ->
        wf_exp ([(X,Typ)] ++ E) (open_te e X)) ->
      wf_exp E (exp_tabs T e)
  | wf_exp_tapp : forall E e T,
      wf_exp E e ->
      wf_typ E T ->
      wf_exp E (exp_tapp e T)
  | wf_exp_let : forall L E e1 e2,
      wf_exp E e1 ->
      (forall x : atom, x `notin` L ->
        wf_exp ([(x,Exp)] ++ E) (open_ee e2 x)) ->
      wf_exp E (exp_let e1 e2)
  | wf_exp_inl : forall E e,
      wf_exp E e ->
      wf_exp E (exp_inl e)
  | wf_exp_inr : forall E e,
      wf_exp E e ->
      wf_exp E (exp_inr e)
  | wf_exp_case : forall L E e1 e2 e3,
      wf_exp E e1 ->
      (forall x : atom, x `notin` L ->
        wf_exp ([(x,Exp)] ++ E) (open_ee e2 x)) ->
      (forall x : atom, x `notin` L ->
        wf_exp ([(x,Exp)] ++ E) (open_ee e3 x)) ->
      wf_exp E (exp_case e1 e2 e3).

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
      sub E (typ_all S1 S2) (typ_all T1 T2)
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
      typing E (exp_abs V e1) (typ_arrow V T1)
  | typing_app : forall T1 E e1 e2 T2,
      typing E e1 (typ_arrow T1 T2) ->
      typing E e2 T1 ->
      typing E (exp_app e1 e2) T2
  | typing_tabs : forall L E V e1 T1,
      (forall X : atom, X `notin` L ->
        typing ([(X, bind_sub V)] ++ E) (open_te e1 X) (open_tt T1 X)) ->
      typing E (exp_tabs V e1) (typ_all V T1)
  | typing_tapp : forall T1 E e1 T T2,
      typing E e1 (typ_all T1 T2) ->
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
      typing E (exp_let e1 e2) T2
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
      typing E (exp_case e1 e2 e3) T
.


(* ********************************************************************** *)
(** * #<a name="values"></a># Values *)

Inductive value : exp -> Prop :=
  | value_abs : forall E T e1,
      wf_exp E (exp_abs T e1) ->
      value (exp_abs T e1)
  | value_tabs : forall E T e1,
      wf_exp E (exp_tabs T e1) ->
      value (exp_tabs T e1)
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
      wf_exp E (exp_app (exp_abs T e1) v2) ->
      value v2 ->
      red (exp_app (exp_abs T e1) v2) (open_ee e1 v2)
  | red_tabs : forall E T1 e1 T2,
      wf_exp E (exp_tapp (exp_tabs T1 e1) T2) ->
      red (exp_tapp (exp_tabs T1 e1) T2) (open_te e1 T2)
  | red_let_1 : forall E e1 e1' e2,
      wf_exp E (exp_let e1 e2) ->
      red e1 e1' ->
      red (exp_let e1 e2) (exp_let e1' e2)
  | red_let : forall E v1 e2,
      wf_exp E (exp_let v1 e2) ->
      value v1 ->
      red (exp_let v1 e2) (open_ee e2 v1)
  | red_inl_1 : forall e1 e1',
      red e1 e1' ->
      red (exp_inl e1) (exp_inl e1')
  | red_inr_1 : forall e1 e1',
      red e1 e1' ->
      red (exp_inr e1) (exp_inr e1')
  | red_case_1 : forall E e1 e1' e2 e3,
      wf_exp E (exp_case e1 e2 e3) ->
      red e1 e1' ->
      red (exp_case e1 e2 e3) (exp_case e1' e2 e3)
  | red_case_inl : forall E v1 e2 e3,
      wf_exp E (exp_case (exp_inl v1) e2 e3)  ->
      value v1 ->
      red (exp_case (exp_inl v1) e2 e3) (open_ee e2 v1)
  | red_case_inr : forall E v1 e2 e3,
      wf_exp E (exp_case (exp_inr v1) e2 e3)  ->
      value v1 ->
      red (exp_case (exp_inr v1) e2 e3) (open_ee e3 v1)
.


(* ********************************************************************** *)
(** * #<a name="auto"></a># Automation *)

Hint Constructors lc wf_typ wf_exp wf_env value red.
Hint Resolve sub_top sub_refl_tvar sub_arrow.
Hint Resolve sub_sum typing_inl typing_inr.
Hint Resolve typing_var typing_app typing_tapp typing_sub.
Hint Resolve typing_inl typing_inr.
