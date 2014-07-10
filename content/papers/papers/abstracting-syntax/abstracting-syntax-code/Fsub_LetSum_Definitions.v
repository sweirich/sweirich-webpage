(** Definition of Fsub (System F with subtyping).

    Authors: Brian Aydemir and Arthur Charguéraud, with help from
    Aaron Bohannon, Jeffrey Vaughan, and Dimitrios Vytiniotis. *)

Require Export Metatheory.
Require Export Common.


(* ********************************************************************** *)
(** * #<a name="syntax"></a># Syntax (pre-terms) *)

Inductive typ : Set :=
  | typ_top : typ
  | typ_bvar : nat -> typ
  | typ_fvar : atom -> typ
  | typ_arrow : typ -> typ -> typ
  | typ_all : typ -> typ -> typ
  | typ_sum : typ -> typ -> typ
.

Inductive exp : Set :=
  | exp_bvar : nat -> exp
  | exp_fvar : atom -> exp
  | exp_abs : typ -> exp -> exp
  | exp_app : exp -> exp -> exp
  | exp_tabs : typ -> exp -> exp
  | exp_tapp : exp -> typ -> exp
  | exp_let : exp -> exp -> exp
  | exp_inl : exp -> exp
  | exp_inr : exp -> exp
  | exp_case : exp -> exp -> exp -> exp
.

Coercion typ_bvar : nat >-> typ.
Coercion typ_fvar : atom >-> typ.
Coercion exp_bvar : nat >-> exp.
Coercion exp_fvar : atom >-> exp.


(* ********************************************************************** *)
(** * #<a name="open"></a># Opening terms *)

Fixpoint open_tt_rec (K : nat) (U : typ) (T : typ)  {struct T} : typ :=
  match T with
  | typ_top => typ_top
  | typ_bvar J => if K === J then U else (typ_bvar J)
  | typ_fvar X => typ_fvar X
  | typ_arrow T1 T2 => typ_arrow (open_tt_rec K U T1) (open_tt_rec K U T2)
  | typ_all T1 T2 => typ_all (open_tt_rec K U T1) (open_tt_rec (S K) U T2)
  | typ_sum T1 T2 => typ_sum (open_tt_rec K U T1) (open_tt_rec K U T2)
  end.

Fixpoint open_te_rec (K : nat) (U : typ) (e : exp) {struct e} : exp :=
  match e with
  | exp_bvar i => exp_bvar i
  | exp_fvar x => exp_fvar x
  | exp_abs V e1 => exp_abs  (open_tt_rec K U V)  (open_te_rec (S K) U e1)
  | exp_app e1 e2 => exp_app  (open_te_rec K U e1) (open_te_rec K U e2)
  | exp_tabs V e1 => exp_tabs (open_tt_rec K U V)  (open_te_rec (S K) U e1)
  | exp_tapp e1 V => exp_tapp (open_te_rec K U e1) (open_tt_rec K U V)
  | exp_let e1 e2 => exp_let (open_te_rec K U e1) (open_te_rec (S K) U e2)
  | exp_inl e1 => exp_inl (open_te_rec K U e1)
  | exp_inr e2 => exp_inr (open_te_rec K U e2)
  | exp_case e1 e2 e3 =>
      exp_case (open_te_rec K U e1) (open_te_rec (S K) U e2) (open_te_rec (S K) U e3)
  end.

Fixpoint open_ee_rec (k : nat) (f : exp) (e : exp)  {struct e} : exp :=
  match e with
  | exp_bvar i => if k === i then f else (exp_bvar i)
  | exp_fvar x => exp_fvar x
  | exp_abs V e1 => exp_abs V (open_ee_rec (S k) f e1)
  | exp_app e1 e2 => exp_app (open_ee_rec k f e1) (open_ee_rec k f e2)
  | exp_tabs V e1 => exp_tabs V (open_ee_rec (S k) f e1)
  | exp_tapp e1 V => exp_tapp (open_ee_rec k f e1) V
  | exp_let e1 e2 => exp_let (open_ee_rec k f e1) (open_ee_rec (S k) f e2)
  | exp_inl e1 => exp_inl (open_ee_rec k f e1)
  | exp_inr e2 => exp_inr (open_ee_rec k f e2)
  | exp_case e1 e2 e3 =>
      exp_case (open_ee_rec k f e1) (open_ee_rec (S k) f e2) (open_ee_rec (S k) f e3)
  end.

Definition open_tt T U := open_tt_rec 0 U T.
Definition open_te e U := open_te_rec 0 U e.
Definition open_ee e1 e2 := open_ee_rec 0 e2 e1.


(* ********************************************************************** *)
(** * #<a name="fv"></a># Free variables *)

Fixpoint fv_tt (T : typ) {struct T} : atoms :=
  match T with
  | typ_top => {}
  | typ_bvar J => {}
  | typ_fvar X => singleton X
  | typ_arrow T1 T2 => (fv_tt T1) `union` (fv_tt T2)
  | typ_all T1 T2 => (fv_tt T1) `union` (fv_tt T2)
  | typ_sum T1 T2 => (fv_tt T1) `union` (fv_tt T2)
  end.

Fixpoint fv_te (e : exp) {struct e} : atoms :=
  match e with
  | exp_bvar i => {}
  | exp_fvar x => {}
  | exp_abs V e1  => (fv_tt V) `union` (fv_te e1)
  | exp_app e1 e2 => (fv_te e1) `union` (fv_te e2)
  | exp_tabs V e1 => (fv_tt V) `union` (fv_te e1)
  | exp_tapp e1 V => (fv_tt V) `union` (fv_te e1)
  | exp_let e1 e2 => (fv_te e1) `union` (fv_te e2)
  | exp_inl e1 => (fv_te e1)
  | exp_inr e1 => (fv_te e1)
  | exp_case e1 e2 e3 => (fv_te e1) `union` (fv_te e2) `union` (fv_te e3)
  end.

Fixpoint fv_ee (e : exp) {struct e} : atoms :=
  match e with
  | exp_bvar i => {}
  | exp_fvar x => singleton x
  | exp_abs V e1 => (fv_ee e1)
  | exp_app e1 e2 => (fv_ee e1) `union` (fv_ee e2)
  | exp_tabs V e1 => (fv_ee e1)
  | exp_tapp e1 V => (fv_ee e1)
  | exp_let e1 e2 => (fv_ee e1) `union` (fv_ee e2)
  | exp_inl e1 => (fv_ee e1)
  | exp_inr e1 => (fv_ee e1)
  | exp_case e1 e2 e3 => (fv_ee e1) `union` (fv_ee e2) `union` (fv_ee e3)
  end.


(* ********************************************************************** *)
(** * #<a name="subst"></a># Substitution *)

Fixpoint subst_tt (Z : atom) (U : typ) (T : typ) {struct T} : typ :=
  match T with
  | typ_top => typ_top
  | typ_bvar J => typ_bvar J
  | typ_fvar X => if X == Z then U else T
  | typ_arrow T1 T2 => typ_arrow (subst_tt Z U T1) (subst_tt Z U T2)
  | typ_all T1 T2 => typ_all (subst_tt Z U T1) (subst_tt Z U T2)
  | typ_sum T1 T2 => typ_sum (subst_tt Z U T1) (subst_tt Z U T2)
  end.

Fixpoint subst_te (Z : atom) (U : typ) (e : exp) {struct e} : exp :=
  match e with
  | exp_bvar i => exp_bvar i
  | exp_fvar x => exp_fvar x
  | exp_abs V e1 => exp_abs  (subst_tt Z U V)  (subst_te Z U e1)
  | exp_app e1 e2 => exp_app  (subst_te Z U e1) (subst_te Z U e2)
  | exp_tabs V e1 => exp_tabs (subst_tt Z U V)  (subst_te Z U e1)
  | exp_tapp e1 V => exp_tapp (subst_te Z U e1) (subst_tt Z U V)
  | exp_let e1 e2 => exp_let (subst_te Z U e1) (subst_te Z U e2)
  | exp_inl e1 => exp_inl (subst_te Z U e1)
  | exp_inr e1 => exp_inr (subst_te Z U e1)
  | exp_case e1 e2 e3 =>
      exp_case (subst_te Z U e1) (subst_te Z U e2) (subst_te Z U e3)
  end.

Fixpoint subst_ee (z : atom) (u : exp) (e : exp) {struct e} : exp :=
  match e with
  | exp_bvar i => exp_bvar i
  | exp_fvar x => if x == z then u else e
  | exp_abs V e1 => exp_abs V (subst_ee z u e1)
  | exp_app e1 e2 => exp_app (subst_ee z u e1) (subst_ee z u e2)
  | exp_tabs V e1 => exp_tabs V (subst_ee z u e1)
  | exp_tapp e1 V => exp_tapp (subst_ee z u e1) V
  | exp_let e1 e2 => exp_let (subst_ee z u e1) (subst_ee z u e2)
  | exp_inl e1 => exp_inl (subst_ee z u e1)
  | exp_inr e1 => exp_inr (subst_ee z u e1)
  | exp_case e1 e2 e3 =>
      exp_case (subst_ee z u e1) (subst_ee z u e2) (subst_ee z u e3)
  end.


(* ********************************************************************** *)
(** * #<a name="lc"></a># Local closure *)

Inductive type : typ -> Prop :=
  | type_top :
      type typ_top
  | type_var : forall X,
      type (typ_fvar X)
  | type_arrow : forall T1 T2,
      type T1 ->
      type T2 ->
      type (typ_arrow T1 T2)
  | type_all : forall L T1 T2,
      type T1 ->
      (forall X : atom, X `notin` L -> type (open_tt T2 X)) ->
      type (typ_all T1 T2)
  | type_sum : forall T1 T2,
      type T1 ->
      type T2 ->
      type (typ_sum T1 T2)
.

Inductive expr : exp -> Prop :=
  | expr_var : forall x,
      expr (exp_fvar x)
  | expr_abs : forall L T e1,
      type T ->
      (forall x : atom, x `notin` L -> expr (open_ee e1 x)) ->
      expr (exp_abs T e1)
  | expr_app : forall e1 e2,
      expr e1 ->
      expr e2 ->
      expr (exp_app e1 e2)
  | expr_tabs : forall L T e1,
      type T ->
      (forall X : atom, X `notin` L -> expr (open_te e1 X)) ->
      expr (exp_tabs T e1)
  | expr_tapp : forall e1 V,
      expr e1 ->
      type V ->
      expr (exp_tapp e1 V)
  | expr_let : forall L e1 e2,
      expr e1 ->
      (forall x : atom, x `notin` L -> expr (open_ee e2 x)) ->
      expr (exp_let e1 e2)
  | expr_inl : forall e1,
      expr e1 ->
      expr (exp_inl e1)
  | expr_inr : forall e1,
      expr e1 ->
      expr (exp_inr e1)
  | expr_case : forall L e1 e2 e3,
      expr e1 ->
      (forall x : atom, x `notin` L -> expr (open_ee e2 x)) ->
      (forall x : atom, x `notin` L -> expr (open_ee e3 x)) ->
      expr (exp_case e1 e2 e3)
.


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

Hint Constructors type expr wf_typ wf_exp wf_env value red.
Hint Resolve sub_top sub_refl_tvar sub_arrow.
Hint Resolve sub_sum typing_inl typing_inr.
Hint Resolve typing_var typing_app typing_tapp typing_sub.
Hint Resolve typing_inl typing_inr.
