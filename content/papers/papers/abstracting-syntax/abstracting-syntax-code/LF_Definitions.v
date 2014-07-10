(** Definition of Fsub (System F with subtyping).
    LF - style version

    Authors: Stephanie Weirich

*)


Axiom skip : False.  
Ltac skip := assert False; [ apply skip | contradiction ].


Require Export Metatheory.

(* ********************************************************************** *)
(** * #<a name="pre"></a># Pre-terms *)

(* Start with the same coalesced syntax from Steve's version *)

Inductive syntax : Set :=
  | bvar  : nat -> syntax
  | fvar  : atom -> syntax
  | typ_top   : syntax
  | typ_arrow : syntax -> syntax -> syntax
  | typ_all   : syntax -> syntax -> syntax
  | exp_abs  : syntax -> syntax -> syntax
  | exp_app  : syntax -> syntax -> syntax
  | exp_tabs : syntax -> syntax -> syntax
  | exp_tapp : syntax -> syntax -> syntax
.

Coercion bvar : nat >-> syntax.
Coercion fvar : atom >-> syntax.


(* ********************************************************************** *)
(** * #<a name="open"></a> Opening terms *)

(* Define and prove all of the same properties for it. *)

Fixpoint open_rec (K : nat) (U : syntax) (T : syntax)  {struct T} : syntax :=
  match T with
  | bvar J      => if K === J then U else (bvar J)
  | fvar X      => fvar X
  | typ_top         => typ_top
  | typ_arrow T1 T2 => typ_arrow (open_rec K U T1) (open_rec K U T2)
  | typ_all T1 T2   => typ_all (open_rec K U T1) (open_rec (S K) U T2)
  | exp_abs V e1  => exp_abs  (open_rec K U V)  (open_rec (S K) U e1)
  | exp_app e1 e2 => exp_app  (open_rec K U e1) (open_rec K U e2)
  | exp_tabs V e1 => exp_tabs (open_rec K U V)  (open_rec (S K) U e1)
  | exp_tapp e1 V => exp_tapp (open_rec K U e1) (open_rec K U V)
  end.

Definition open T U := open_rec 0 U T.
Definition exp := syntax.
Definition typ := syntax.

(* ********************************************************************** *)
(** * #<a name="lc"></a># Local closure *)

Inductive lc : syntax -> Prop :=
  | type_top :
      lc typ_top
  | type_var : forall X,
      lc (fvar X)
  | type_arrow : forall T1 T2,
      lc T1 ->
      lc T2 ->
      lc (typ_arrow T1 T2)
  | type_all : forall L T1 T2,
      lc T1 ->
      (forall X : atom, X `notin` L -> lc (open T2 X)) ->
      lc (typ_all T1 T2)
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
.

Hint Resolve type_top type_var type_arrow expr_app expr_tapp.

(* ********************************************************************** *)

Fixpoint fv (T : syntax) {struct T} : atoms :=
  match T with
  | typ_top         => {}
  | bvar J      => {}
  | fvar X      => singleton X
  | typ_arrow T1 T2 => (fv T1) `union` (fv T2)
  | typ_all T1 T2   => (fv T1) `union` (fv T2)
  | exp_abs V e1  => (fv V) `union` (fv e1)
  | exp_app e1 e2 => (fv e1) `union` (fv e2)
  | exp_tabs V e1 => (fv V) `union` (fv e1)
  | exp_tapp e1 V => (fv V) `union` (fv e1)
  end.

(* ********************************************************************** *)
(** * #<a name="subst"></a># Substitution *)

Fixpoint subst (Z : atom) (U : typ) (T : typ) {struct T} : typ :=
  match T with
  | typ_top     => typ_top
  | bvar J      => bvar J
  | fvar X      => if X == Z then U else T
  | typ_arrow T1 T2 => typ_arrow (subst Z U T1) (subst Z U T2)
  | typ_all T1 T2   => typ_all (subst Z U T1) (subst Z U T2)
  | exp_abs V e1  => exp_abs  (subst Z U V)  (subst Z U e1)
  | exp_app e1 e2 => exp_app  (subst Z U e1) (subst Z U e2)
  | exp_tabs V e1 => exp_tabs (subst Z U V)  (subst Z U e1)
  | exp_tapp e1 V => exp_tapp (subst Z U e1) (subst Z U V)
  end.


(* ********************************************************************** *)
(** * #<a name="properties"></a># Properties of opening and substitution *)


Lemma open_rec_aux : forall T j V i U,
  i <> j ->
  open_rec j V T = open_rec i U (open_rec j V T) ->
  T = open_rec i U T.
Proof with eauto*.
  induction T; intros j V i U Neq H; simpl in *; inversion H; f_equal...
  Case "typ_bvar".
    destruct (j === n)... destruct (i === n)...
Qed.

Lemma open_rec_trivial : forall T U k,
  lc T ->
  T = open_rec k U T.
Proof with auto*.
  intros T U k Htyp. revert k.
  induction Htyp; intros k; simpl; f_equal...
  Case "typ_all".
    unfold open in *.
    pick fresh X for L .
    apply (open_rec_aux T2 0 (fvar X)).
    eauto*.
    eauto*.
  Case "expr_abs (body)".
    unfold  open in *.
    pick fresh x for L.
    apply (open_rec_aux e1 0 (fvar x))...
  Case "expr_tabs (body)".
    unfold  open in *.
    pick fresh X for L.
    apply (open_rec_aux e1 0 (fvar X))...
Qed.

(** If a name is fresh for a term, then substituting for it is the
    identity. *)

Lemma subst_fresh : forall Z U T,
   Z `notin` fv T ->
   T = subst Z U T.
Proof with auto*.
  induction T; simpl; intro H; f_equal...
  Case "typ_fvar".
    destruct (a == Z)...
    absurd_hyp H; decideFSet.
Qed.

(** Substitution commutes with opening under certain conditions.  This
    lemma depends on the fact that opening a locally closed term is
    the identity. *)

Lemma subst_open_rec : forall T1 T2 X P k,
  lc P ->
  subst X P (open_rec k T2 T1) =
    open_rec k (subst X P T2) (subst X P T1).
Proof with auto*.
  intros T1 T2 X P k WP. revert k.
  induction T1; intros k; simpl; f_equal...
  Case "typ_bvar".
    destruct (k === n); subst...
  Case "typ_fvar".
    destruct (a == X); subst... apply open_rec_trivial...
Qed.

(** The next lemma is a direct corollary of the immediately preceding
    lemma---the index is specialized to zero. *)


Lemma subst_open : forall T1 T2 (X:atom) P,
  lc P ->
  subst X P (open T1 T2) = open (subst X P T1) (subst X P T2).
Proof with auto*.
  intros.
  unfold open.
  apply subst_open_rec...
Qed.


(** The next lemma is a direct corollary of the immediately preceding
    lemma---here, we're opening the term with a variable.  By
    symmetry, the conclusion is equivalent to
<<
  subst X U (open T Y) = open (subst X U T) Y .
>>  In practice, this lemma seems to be needed as a left-to-right
    rewrite rule, when stated in its current form. *)

Lemma subst_open_var : forall (X Y:atom) P T,
  Y <> X ->
  lc P ->
  open (subst X P T) Y = subst X P (open T Y).
Proof with auto*.
  intros X Y P T Neq Wu.
  unfold open.
  rewrite subst_open_rec...
  simpl.
  destruct (Y == X)...
Qed.

(** The next lemma states that opening a term is equivalent to first
    opening the term with a fresh name and then substituting for the
    name.  This is actually the strengthened induction hypothesis for
    the version we use in practice. *)

Lemma subst_intro_rec : forall X T2 U k,
  X `notin` fv T2 ->
  open_rec k U T2 = subst X U (open_rec k (fvar X) T2).
Proof with auto*.
  induction T2; intros U k Fr; simpl in *; f_equal...
  Case "typ_bvar".
    destruct (k === n)... simpl. destruct (X == X)...
  Case "typ_fvar".
    destruct (a == X)... absurd_hyp Fr; decideFSet.
Qed.

(** The next lemma is a direct corollary of the immediately preceding
    lemma---the index is specialized to zero.  *)

Lemma subst_intro : forall X T2 U,
  X `notin` fv T2 ->
  open T2 U = subst X U (open T2 X).
Proof with auto*.
  intros.
  unfold open.
  apply subst_intro_rec...
Qed.

(* *********************************************************************** *)

Lemma notin_fv_tt_open : forall (Y X : atom) T,
  X `notin` fv (open T Y) ->
  X `notin` fv T.
Proof.
 intros Y X T. unfold open.
 generalize 0.
 induction T; simpl; intros k Fr; notin_simpl; eauto 4.
Qed.


(* *********************************************************************** *)
(** * #<a name="lc"></a># Local closure is preserved under substitution *)

Lemma subst_lc : forall Z P T,
  lc T ->
  lc P ->
  lc (subst Z P T).
Proof with auto*.
  intros Z P T HT HP.
  induction HT; simpl...
  Case "type_fvar".
    destruct (X == Z)...
  Case "type_all".
    eapply type_all with (L := (L `union` singleton Z `union` fv T1 `union` fv T2)); eauto.
    intros Y Fr.
    rewrite subst_open_var...
  Case "expr_abs".
    eapply expr_abs with (L := (L `union` singleton Z `union` fv T `union` fv e1)); eauto.
    intros.
    rewrite subst_open_var...
  Case "expr_tabs".
    eapply expr_tabs with (L := (L `union` singleton Z `union` fv T `union` fv e1)); eauto.
    intros.
    rewrite subst_open_var...
Qed.

(* ********************************************************************** *)


Definition body_e (e : exp) :=
  exists L, forall x : atom, x `notin` L -> lc (open e x).

Lemma open_body_e : forall e1 e2,
  body_e e1 -> lc e2 -> lc (open e1 e2).
Proof.
  intros e1 e2 [L H] J.
  pick fresh x for (L `union` fv e1).
  rewrite (subst_intro x); auto using subst_lc.
Qed.


(* ********************************************************************** *)
(* ********************************************************************** *)
(* ********************************************************************** *)
(** * #<a name="env"></a># Environments *)


(* Now, next step is to list all of the possible hypothetical judgments 
   that can appear in the environment. *)

Inductive judgment : Set := 
 | syn : judgment
 | wf_typ : typ -> judgment
 | wf_exp : exp -> judgment
 | sub    : typ -> typ -> judgment
 | typing : exp -> typ -> judgment
.

(* Define some infrastructure ops/lemmas for these judgments. 
   Maybe it makes sense to add them to "syntax" above? *)

Definition fv_j k := 
  match k with 
    | syn => {}
    | wf_typ T => fv T
    | wf_exp E => fv E
    | sub S1 T1 => fv S1 `union` fv T1
    | typing E T => fv E `union` fv T
  end.

Definition open_j (k:judgment)(u:syntax) :=
  match k with 
    | syn => syn
    | wf_typ T => wf_typ (open T u)
    | wf_exp E => wf_exp (open E u)
    | sub S1 T1 => sub (open S1 u) (open T1 u)
    | typing E T => typing (open E u) (open T u)
  end.

Definition subst_j (x:atom) (u:syntax) (k:judgment) :=
  match k with 
 | syn => syn
 | wf_typ T => wf_typ (subst x u T)
 | wf_exp E => wf_exp (subst x u E)
 | sub S1 T1  => sub (subst x u S1) (subst x u T1)
 | typing E T => typing (subst x u E) (subst x u T)
  end.

Inductive lc_j : judgment -> Prop :=
 | lc_syn : lc_j syn
 | lc_wf_typ : forall T, lc T -> lc_j (wf_typ T)
 | lc_wf_exp : forall T, lc T -> lc_j (wf_exp T)
 | lc_sub    : forall S T, lc S -> lc T -> lc_j (sub S T)
 | lc_typing : forall E T, lc E -> lc T -> lc_j (typing E T)
.

Hint Constructors lc_j.

Lemma subst_lc_j : forall X P J, 
  lc P -> lc_j J -> lc_j (subst_j X P J).
intros.
  inversion H0; subst; eauto;
  inversion H0; subst; simpl; eauto using subst_lc.
Qed.


Lemma subst_j_fresh : forall x P J, 
  x `notin` fv_j J -> 
  J = subst_j x P J .
Proof.
  intros. destruct J;
    simpl in *; f_equal; eauto using subst_fresh.
Qed.

(* ********************************************************************** *)
(* ********************************************************************** *)

(* environments are like LF contexts, lists of hypothetical judgments. *)

Notation env := (list (atom * judgment)).
Notation empty := (@nil (atom * judgment)).

(* ********************************************************************** *)
(** * #<a name="wf"></a># Well-formedness for environments *)

(* I'm not sure what restrictions we want to place about these LF-like environments. 
   or even where we would like to enforce them. 

   Perhaps we would like to show that all of the free variables in the
   hypotheses are bound earlier in the context.
 *)

Inductive okE : env -> Prop :=
| okE_empty :
  okE empty
| okE_push : forall E X J,
  okE E -> X `notin` dom E -> AtomSet.F.Subset (fv_j J) (dom E) -> okE (E & X ~ J).

Lemma ok_from_okE : forall E, okE E -> ok E.
Proof. 
 induction 1; eauto.
Qed.

Hint Constructors okE.
Hint Resolve ok_from_okE.

(* A stronger restriction, might require that they be bound as syntax. *)

Inductive okE2 : env -> Prop :=
| okE2_empty :
  okE2 empty
| okE2_push : forall E X J,
  okE2 E -> X `notin` dom E -> 
  (forall y, y `in` fv_j J -> binds y syn E) ->
  okE2 (E & X ~ J).

Lemma ok_from_okE2 : forall E, okE2 E -> ok E.
Proof. 
 induction 1; eauto.
Qed.
Hint Constructors okE2.
Hint Resolve ok_from_okE2.

(* ********************************************************************** *)

(* As we're going to be adding multiple variables at once to the context, 
   we define a few helper propositions. *)

Definition fresh2 (X Y: atom) L := 
  (X <> Y /\ X `notin` L /\ Y `notin` L).

Definition fresh3 (X Y Z: atom) L := 
  (X <> Y /\ X <> Z /\ Y <> Z /\ X `notin` L /\ Y `notin` L /\ Z `notin` L).

Hint Unfold fresh2.
Hint Unfold fresh3.

(* ********************************************************************** *)

(* Now, the definition of the semantics of the program. *)

Inductive judge : env -> judgment -> Prop :=

  (* Hypothetical judgment *)
  | judge_var : forall E X J,  
      ok E -> lc_j J ->
      binds X J E ->
      judge E J

  (* Need this for the substitution lemma. Could make it take 
     actualy syntax as an argument, but I don't see that necessary
     yet. *)
  | syn_triv : forall E, judge E syn

  (* Well formed types *)
  | wf_typ_top : forall E,
      judge E (wf_typ typ_top)
  | wf_typ_arrow : forall E T1 T2,
      judge E (wf_typ T1) ->
      judge E (wf_typ T2) ->
      judge E (wf_typ (typ_arrow T1 T2))
  | wf_typ_all : forall L E T1 T2,
      judge E (wf_typ T1) ->
      (forall X Y, fresh2 X Y L ->
        judge (E & (X ~ syn) & (Y ~ wf_typ X)) (wf_typ (open T2 X))) -> 
      judge E (wf_typ (typ_all T1 T2))

  (* Declarative subtyping *)      
  | subtype_top : forall E T,
      judge E (wf_typ T) ->
      judge E (sub T typ_top)
  | subtype_refl : forall E T, 
      judge E (wf_typ T) ->
      judge E (sub T T)
  | subtype_trans : forall T2 E T1 T3,
      judge E (sub T1 T2) -> 
      judge E (sub T2 T3) ->
      judge E (sub T1 T3)
  | subtype_arrow : forall E S1 S2 T1 T2,
      judge E (sub T1 S1) ->
      judge E (sub S2 T2) -> 
      judge E (sub (typ_arrow S1 S2) (typ_arrow T1 T2))
  | subtype_all : forall L E S1 S2 T1 T2,
      judge E (sub T1 S1) -> 
      (* note: I keep going back and forth about whether I need to include 
         Y ~ wf_typ X here. Should be able to translate any 
         sub X T1 derivation into a wf_typ derivation. 
         I guess we do need them b/c we need to assume that they are available to 
         show that they are available.
         *)
     (forall X Y Z, fresh3 X Y Z L ->
        judge (E & X ~ syn & Y ~ wf_typ X & Z ~ sub X T1) (sub (open S2 X) (open T2 X))) ->
      judge E (sub (typ_all S1 S2) (typ_all T1 T2))

  (* Well formed terms *)
  (* Commented out for now to make experimenting easier. Not up to date 
     with conventions above. *)
(*  | wf_exp_abs : forall E,
      judge E (wf_typ V) ->
      (forall X, X `notin` L -> 
        judge (E & X ~ wf_exp X) (wf_exp (open e1 X))) ->
      judge E (wf_exp (exp_abs V e1))
  | wf_exp_app : forall E T1 T2,
      judge E (wf_exp e1) ->
      judge E (wf_exp e2) ->
      judge E (wf_exp (exp_app e1 e2))
  | wf_exp_tabs : forall E,
      judge E (wf_typ V) ->
      (forall X, X `notin` L -> 
        judge (E & X ~ wf_typ X) (wf_exp (open e1 X))) ->
      judge E (wf_exp (exp_tabs V e1))
  | wf_exp_tapp : forall E e1 T2,
      judge E (wf_exp e1) ->
      judge E (wf_typ T2) ->
      judge E (wf_exp (exp_tapp e1 e2)) *)

 (* Typing rules here. *)
(*  | typing_abs : forall L E V e1 T1,
      judge E (wf_typ V) ->
      (forall X Y, fresh2 X Y L -> 
        judge (E & X ~ wf_exp X & Y ~ typing X V) (typing (open e1 X) T1)) ->
      judge E (typing (exp_abs V e1) (typ_arrow V T1))
  | typing_app : forall T1 E e1 e2 T2,
      judge E (typing e1 (typ_arrow T1 T2)) ->
      judge E (typing e2 T1) ->
      judge E (typing (exp_app e1 e2) T2)
  | typing_tabs : forall L E V e1 T1,
      judge E (wf_typ V) ->
      (forall X Y, fresh2 X Y L ->
        judge (E & X ~ wf_typ X & Y ~ sub X V) (typing (open e1 X) (open T1 X))) ->
      judge E (typing (exp_tabs V e1) (typ_all V T1))
  | typing_tapp : forall T1 E e1 T T2,
      judge E (typing e1 (typ_all T1 T2)) ->
      judge E (sub T T1) ->
      judge E (typing (exp_tapp e1 T) (open T2 T))
  | typing_sub : forall S E e T,
      judge E (typing e S) ->
      judge E (sub S T) ->
      judge E (typing e T) *)
. 

Hint Resolve judge_var syn_triv wf_typ_top wf_typ_arrow subtype_top subtype_refl 
  subtype_arrow 
  (* typing_app typing_tapp *)
.

(* ********************************************************************** *)
(** * #<a name="pick_fresh"></a># The "[pick fresh]" tactic *)

Ltac gather_atoms :=
  let A := gather_atoms_with (fun x : atoms => x) in
  let B := gather_atoms_with (fun x : atom => singleton x) in
  let C := gather_atoms_with (fun x : syntax => fv x) in
  let D := gather_atoms_with (fun x : judgment => fv_j x) in
  let F := gather_atoms_with (fun x : env => dom x) in
  constr:(A `union` B `union` C `union` D `union` F).

Tactic Notation "pick" "fresh" ident(x) :=
  let L := gather_atoms in (pick fresh x for L).

Tactic Notation
      "pick" "fresh" ident(atom_name) "and" "apply" constr(lemma) :=
  let L := gather_atoms in
    apply cofinite lemma as atom_name excluding L.

(* ********************************************************************** *)

(* Note: could use a tactic that performs inversion on all judgments of a particular 
   form in the hypothesis list. *)

(* Derivable judgements are locally closed. *)

Lemma lc_from_j : forall E J,
  judge E J -> lc_j J.
intros E J H; induction H; 
  try (inversion IHjudge);
  try (inversion IHjudge1);
  try (inversion IHjudge2); eauto.
  Case "wft_all".
    apply lc_wf_typ.
    pick fresh X and apply type_all; eauto.
    assert (lc_j (wf_typ (open T2 X))).
      pick fresh Y.
      eapply H1 with (X := X)(Y:=Y); eauto.
    inversion H4. auto.
  Case "sub_all".
    apply lc_sub.
    pick fresh X and apply type_all; eauto.
    assert (lc_j (sub (open S2 X) (open T2 X))).
      pick fresh Y.
      pick fresh Z.
      eapply H1 with (X:=X)(Y:=Y)(Z:=Z); eauto.
      skip. (* reasoning about fresh 3 *)
    inversion H6. auto.
    pick fresh X and apply type_all; eauto.
    assert (lc_j (sub (open S2 X) (open T2 X))).
      pick fresh Y.
      pick fresh Z.
      eapply H1 with (X:=X)(Y:=Y)(Z:=Z); eauto.
      skip. (* reasoning about fresh 3 *)
    inversion H6. auto.
(*  Case "typing_abs".
    apply lc_typing.
    pick fresh X and apply expr_abs; eauto.
    assert (lc_j (typing (open e1 X) T1)).
      eapply H1 with (X := X); eauto.
    inversion H4. auto.
    pick fresh X. apply type_arrow; eauto.
    assert (lc_j (typing (open e1 X) T1)).
      eapply H1 with (X := X); eauto.
    inversion H4. auto.
  Case "typing app".
    subst. inversion H4. auto.
  Case "typing_tabs".
    apply lc_typing.
    pick fresh X and apply expr_tabs; auto.
    assert (lc_j (typing (open e1 X) (open T1 X))).
      eapply H1 with (X := X); eauto.
    inversion H4.  auto.
    pick fresh X and apply type_all; eauto.
    assert (lc_j (typing (open e1 X) (open T1 X))).
      eapply H1 with (X := X); eauto.
    inversion H4.  auto.
  Case "typing tapp".
    subst. 
    apply lc_typing. auto.
    inversion H4.
    assert (lc (open T2 T)).  
    apply open_body_e; auto. unfold body_e. exists L. auto.
    eauto. *)
Qed.

Lemma j_weaken : forall J E F G, 
  judge (E & G) J -> 
  ok (E & F & G) -> 
  judge (E & F & G) J.
Proof with simpl_env; auto.
  intros T E F G Hwf_typ Hk.
  remember (E & G) as K. generalize dependent E. revert F G.
  induction Hwf_typ; intros F G E0; eauto 4.
  Case "hyp".
    intros Hok Heq; subst.
    eauto using binds_weaken, ok_from_okE.
  Case "type_all".
    intros Hok Heq; subst.
    pick fresh X and apply wf_typ_all...
    intros X Y Fr2.
    rewrite_env (E0 & F & (G & X ~ syn & Y ~ wf_typ X)).
    eapply H0...  
    unfold fresh2 in *; eauto.
    unfold fresh2 in *.
    decompose record Fr2.
    eauto.
  Case "sub_trans".
    intros Hok Heq; subst.
    eapply subtype_trans with (T2 := T2); eauto.
  Case "sub_all".
    intros Hok Heq; subst.
    pick fresh X and apply subtype_all; auto.
    intros X Y Z Fr.  unfold fresh3 in Fr; decompose record Fr; clear Fr. 
    rewrite_env (E0 & F & (G & X ~ syn & Y ~ wf_typ X & Z ~ sub X T1)).
    eapply H0...
    skip. (* fresh3 *)
(*  Case "typing_abs".
    intros Hok Heq; subst...
    pick fresh X and apply typing_abs; auto...
    eapply IHHwf_typ.
    pose (J := ok_map_alt sub_to_wft Hok).
    simpl_env in J... simpl_env. auto.
    rewrite_env (E0 & F & (G & X ~ typing X V)).
    eapply H0... auto.
  Case "typing_tabs".
    intros Hok Heq; subst.
    pick fresh X and apply typing_tabs; auto.
    simpl_env. eapply IHHwf_typ.
    pose (J := ok_map_alt sub_to_wft Hok).
    simpl_env in J. auto. simpl_env. auto.
    rewrite_env (E0 & F & (G & X ~ sub X V)).
    eapply H0...
  Case "typing_sub".
    intros Hok Heq; subst.
    eapply typing_sub; eauto.*)
Qed.

Lemma j_weaken_right : forall J E F, 
  judge E J ->
  ok (E & F) ->
  judge (E & F) J.
Proof.
  intros.
  rewrite_env (E & F & empty).
  auto using j_weaken.
Qed.

(* Substituting for syntax, which may appear in the environment 
   and judgments. *)

Lemma j_subst : forall X P E F J,
  okE2 (E & X ~ syn & F) ->
  judge (E & X ~ syn & F) J ->
  judge (E & (map (subst_j X P) F)) (subst_j X P J).
Proof with simpl_env; eauto.
  intros X P E F J OK D1.
  remember (E & X ~ syn & F) as G. 
  generalize dependent F.
  induction D1; intros F Eq; subst; simpl...
  Case "hyp".
    binds_cases H1.
     Subcase "X0 in E". (* need to show X `notin` fv J using okE2. *)
      skip.
     Subcase "X=X0".
      subst. simpl. eauto.
     Subcase "X in F".
      skip.
  Case "wf_all".
    skip.
  Case "trans".
    skip.
  Case "sub_all".
    skip.
Qed.

(* Substitution for derivations in derivations.*)

Lemma j_strengthen : forall E Z J1 F J2,  
  ok (E & Z ~ J1 & F) ->
  judge (E & Z ~ J1 & F) J2  ->
  judge E J1 ->
  J1 <> syn -> (* Somehow need to rule out Z in fv F or in fv J2 *)
  judge (E & F) J2.
Proof with simpl_env; eauto.
  intros E Z J1 F J2 Ok D2. 
  remember (E & Z ~ J1 & F) as G.
  generalize dependent F.
  generalize dependent J1.
  generalize dependent E.
  induction D2; intros E0 J1 F EQ D1; subst; simpl subst...
  Case "hyp".
    destruct (X == Z).
      Case "X=Z".
      subst. binds_get H.
      apply j_weaken_right...
      Case "X<>Z".
      binds_cases H...
  Case "wf_typ_all".
   pick fresh X and apply wf_typ_all...
   rewrite_env (E0 & (F & X ~ wf_typ X)).
   eapply H0 with (X := X)...
  Case "sub_top".
   eapply subtype_top.
   simpl_env.
   eapply IHD2. eapply ok_map_alt. auto.
   simpl_env. eauto.
  Case "sub_trans".
   eapply subtype_trans with (T2 := T2); eauto.
  Case "sub_all".
   pick fresh X and apply subtype_all...
   rewrite_env (E & (F & X ~ sub X T1)).
   eapply H0 with (X:=X)...
  Case "typing_abs".
   pick fresh X and apply typing_abs...
   rewrite_env (E & (F & X ~ typing X V)).
   eapply H0 with (X := X)...
  Case "typing_tabs".
   pick fresh X and apply typing_tabs...
   rewrite_env (E & (F & X ~ sub X V)).
   eapply H1 with (X:= X)...
  Case "typing_sub".
   eapply typing_sub; auto.
Qed.


(* Trying to figure out the right version of the 
   renaming lemma *)

Lemma j_rename1 : forall x y E F J1 J2, 
  x `notin` dom E -> y `notin` dom E ->
  judge (E & x ~ syn & F) J2 -> 
  judge (E & y ~ syn & (map subst_j x y F)) (subst_j x y J2).
Admitted.

(* Need something like this, not sure how to prove it 
   with the substitution lemma. *)
Lemma j_rename2 : forall x y E F J1 J2, 
  x `notin` dom E -> y `notin` dom (E & F) ->
  judge (E & x ~ J1 & F) J2 -> 
  judge (E & y ~ J2 & F) J2
Admitted.


(* Need to use above to prove exists version of rules. *)
Lemma wf_typ_all_ex : forall X Y E T1 T2,
      X `notin` dom E -> Y `notin` dom E -> X <> Y -> 
      X `notin` fv T2 -> Y `notin fv T2 ->
      judge E (wf_typ T1) ->
      judge (E & (X ~ syn) & (Y ~ wf_typ X)) (wf_typ (open T2 X))) -> 
      judge E (wf_typ (typ_all T1 T2)).
Admitted.

(* ********************************************************************** *)
(* ********************************************************************** *)
(* ********************************************************************** *)

(* Proofs about the system itself, using the infrastructure above. *)

(* wf_typ doesn't depend on subtyping hypotheses. *)
Lemma subord1 : 
  forall E X F S T T1, 
  judge (E & X ~ sub S T & F) (wf_typ T1) -> 
  judge (E & F) (wf_typ T1).
intros E X F S T T1 H.
remember (E & X ~ sub S T & F) as E0.
remember (wf_typ T1) as J.
generalize dependent T1.
generalize dependent F.
induction H; intros F Eq S0 HeqJ; inversion HeqJ; subst; eauto.
Case "var".
  assert (binds X0 (wf_typ S0) (E & F)).
    binds_cases H0; auto.
  assert (ok (E & F)).
    eapply ok_remove; eauto.
  eauto.
Case "all".
  pick fresh Y and apply wf_typ_all; eauto.
  rewrite_env (E & (F & Y ~ wf_typ Y)); eauto.
Qed.
  
  
(* subtyping implies types are well formed. *)
Lemma regularity : forall E S T, 
  ok E ->
  (* Worlds assumption *)
  (forall X S T, binds X (sub S T) E -> judge E (wf_typ S) /\ judge E (wf_typ T)) ->
  judge E (sub S T) -> 
  judge E (wf_typ S) /\ judge E (wf_typ T).
intros E S T Ok World D.
remember (sub S T) as J.
generalize dependent S.
generalize dependent T.
induction D; intros S0 T0 HeqJ; inversion HeqJ; subst; eauto.
Case "trans".
 destruct (IHD1 Ok World T2 T0); auto.
 destruct (IHD2 Ok World S0 T2); auto. 
Case "arrow".
 destruct (IHD1 Ok World S1 T1); auto.
 destruct (IHD2 Ok World T2 S2); auto.
Case "all".
 destruct (IHD Ok World S1 T1). auto.
 split. 
 (* This proof would be easier with exists-intro rule. *)
 pick fresh X and apply wf_typ_all. auto.
 pick fresh Y.
 assert (Fr2 : fresh2 X Y L). auto.
 assert (Ok2 : ok (E & X ~ wf_typ X & Y ~ sub X T1)). auto.
 assert (forall (X0 : atom) (S T : typ),
          binds X0 (sub S T) (E & X ~ wf_typ X & Y ~ sub X T1) ->
          judge (E & X ~ wf_typ X & Y ~ sub X T1) (wf_typ S) /\
          judge (E & X ~ wf_typ X & Y ~ sub X T1) (wf_typ T)).
 Case "assertion.".
   intros X0 S T B.
   binds_cases B.
   Case "X0 is in E".
   destruct (World X0 S T); auto.
   split.
     eapply j_weaken_right; eauto.
     eapply j_weaken_right; eauto.
     eapply j_weaken_right; eauto.
     eapply j_weaken_right; eauto.
   Case "X0 is Y".
     inversion H5; subst.
     split.
     eauto.
     eapply j_weaken_right; auto.
     eapply j_weaken_right; auto.
destruct (H0 X Y Fr2 Ok2 H3 (open T2 X)(open S2 X)); auto.
rewrite_env (E & X ~ wf_typ X & empty).
eapply subord1 with (X := Y) (S:=X)(T:= T1). 
auto.
 pick fresh X and apply wf_typ_all. auto.
 pick fresh Y.
 assert (Fr2 : fresh2 X Y L). auto.
 assert (Ok2 : ok (E & X ~ wf_typ X & Y ~ sub X T1)). auto.
 assert (forall (X0 : atom) (S T : typ),
          binds X0 (sub S T) (E & X ~ wf_typ X & Y ~ sub X T1) ->
          judge (E & X ~ wf_typ X & Y ~ sub X T1) (wf_typ S) /\
          judge (E & X ~ wf_typ X & Y ~ sub X T1) (wf_typ T)).
 Case "assertion.".
   intros X0 S T B.
   binds_cases B.
   Case "X0 is in E".
   destruct (World X0 S T); auto.
   split.
     eapply j_weaken_right; eauto.
     eapply j_weaken_right; eauto.
     eapply j_weaken_right; eauto.
     eapply j_weaken_right; eauto.
   Case "X0 is Y".
     inversion H5; subst.
     split.
     eauto.
     eapply j_weaken_right; auto.
     eapply j_weaken_right; auto.
destruct (H0 X Y Fr2 Ok2 H3 (open T2 X)(open S2 X)); auto.
rewrite_env (E & X ~ wf_typ X & empty).
eapply subord1 with (X := Y) (S:=X)(T:= T1). 
auto.
Qed.


(* When are environments well-formed? This is like the 
   worlds assumption above. Perhaps we should use it instead? *)

Inductive wf_env : env -> Prop :=
| wf_env_empty :
  wf_env empty
| wf_env_syntax : forall E X,
  wf_env E -> X `notin` dom E ->
  wf_env (E & X ~ syn)
| wf_env_wf_typ : forall E X T,
  wf_env E -> X `notin` dom E ->
  judge E (wf_typ T) ->
  wf_env ( E & X ~ (wf_typ T))
| wf_env_sub : forall (E : env) (X : atom) (T1 : typ) (T2:typ),
  wf_env E -> X `notin` dom E -> 
  judge E (wf_typ T1) -> judge E (wf_typ T2) ->
  wf_env (E & X ~ (sub T1 T2))
| wf_env_typ : forall (E : env) (X : atom) (T : typ) (e:exp),
  wf_env E -> X `notin` dom E -> judge E (wf_typ T) ->  
  wf_env (E & X ~ typing e T).


(* General form of narrowing for subtyping. *)
Lemma narrowing : forall E F X T1 T2 J, 
  judge (E & x ~ sub T1 T2 & F) J ->
  judge E (sub T0 T1) ->
  judge (E & x ~ sub T0 T2 & F) J.
Admitted.



(**************************STOP HERE********************************)

(* old proof script. *)
Lemma j_subst : forall X P E F J2,
  lc P ->
  X `notin` dom (E & F) ->
  judge (E & F) J2 ->
  judge ((map (subst_j X P) E) & (map (subst_j X P) F)) (subst_j X P J2).
Proof with simpl_env; eauto.
  intros X P E F J2 LC  Fr D1.
  remember (E & F) as G. generalize dependent F.
  induction D1; intros F Eq; subst; simpl...
  Case "hyp".
    eapply judge_var with (X := X0).
    rewrite <- map_concat.
    apply ok_map_alt...
    rewrite <- map_concat.
    apply binds_map...
    apply subst_lc_j; auto.
  Case "all".
    pick fresh Y and apply wf_typ_all...
    assert (Y <> X) by notin_solve.
    rewrite subst_open_var; eauto.    
    replace (Y ~ (wf_typ Y)) with (map (subst_j X P) (Y ~ wf_typ Y)); auto.
    rewrite_env (map (subst_j X P) E & 
                 map (subst_j X P) (F & Y ~ wf_typ Y)); auto.
    simpl subst_j in H0.
    eapply H0 with (X0:=Y); auto.
    simpl. auto.
    simpl. destruct (Y == X).
         contradiction.
         auto.
  Case "trans".
    eapply subtype_trans with (T2 := subst X P T2)...
  Case "subtype_all".
    pick fresh Y and apply subtype_all...
    intros X0 Y Fr2.
    assert (Y <> X) by notin_solve.
    rewrite subst_open_var; eauto.
    rewrite subst_open_var; eauto.
    replace (Y ~ sub Y (subst X P T1)) with (map (subst_j X P) (Y ~ sub Y T1)).
    rewrite_env (map (subst_j X P) E & map (subst_j X P) (F & Y ~ sub Y T1)); auto.
    simpl subst_j in H0.
    eapply H0 with (X0 := Y). auto.
    simpl. auto.
    simpl. destruct (Y == X).
         contradiction.
         auto.
    simpl. destruct (Y == X).
         contradiction.
         auto.
(*  Case "typing_abs".
    pick fresh Y and apply typing_abs...
    assert (Y <> X) by notin_solve. 
    rewrite subst_open_var; eauto.
    replace (Y ~ typing Y (subst X P V)) with (map (subst_j X P) (Y ~ typing Y V)).
    rewrite_env (map (subst_j X P) E & map (subst_j X P) (F & Y ~ typing Y V)); auto.
    simpl subst_j in H0.
    eapply H0 with (X0 := Y). auto.
    simpl. auto. auto.
    simpl. destruct (Y == X).
         contradiction.
         auto.
 Case "typing_app".
    simpl subst_j in *.
    eapply typing_app; eauto.
 Case "typing_tabs".
    pick fresh Y and apply typing_tabs...
    apply subst_lc; auto.
    assert (Y <> X) by notin_solve.
    rewrite subst_open_var; eauto.
    rewrite subst_open_var; eauto.
    replace (Y ~ sub Y (subst X P V)) with (map (subst_j X P) (Y ~ sub Y V)).
    rewrite_env (map (subst_j X P) E & map (subst_j X P) (F & Y ~ sub Y V)); auto.
    simpl subst_j in H1.
    eapply H1 with (X0 := Y). auto. 
    simpl. auto. auto.
    simpl.
       destruct (Y == X).
         contradiction.
         auto.
 Case "typing_tapp".
   simpl subst_j in *.
   rewrite subst_open; auto.
   eapply typing_tapp; eauto.
 Case "typing_sub".    
   simpl subst_j in *.
   eapply typing_sub; eauto. *)
Qed.

   
  


(* ********************************************************************** *)
(* Algorithmic subtyping. Mixing two forms together. *)

Notation asub_env := (list (atom * syntax)).
Notation asub_empty := (@nil (atom * syntax)).

Fixpoint asub_env_to_env (E : asub_env) : env := 
  match E with 
    | nil          => nil
    | (a,ty)::rest => 
            (a, (sub (fvar a) ty)) :: 
                          asub_env_to_env rest
  end.

(* 
Coercion asub_env_to_env : asub_env >-> list (atom * judgement). 
*)

Inductive asub : asub_env -> typ -> typ -> Prop :=
  | asub_top : forall (E:asub_env) S,
      judge (asub_env_to_env E) (wf_typ S) ->
      asub E S typ_top
  | asub_refl_tvar : forall (E:asub_env) X,
      judge (asub_env_to_env E) (wf_typ (fvar X)) ->
      asub E (fvar X) (fvar X)
  | asub_trans_tvar : forall U E T X,
      binds X U E ->
      asub E U T ->
      asub E (fvar X) T
  | asub_arrow : forall E S1 S2 T1 T2,
      asub E T1 S1 ->
      asub E S2 T2 ->
      asub E (typ_arrow S1 S2) (typ_arrow T1 T2)
  | asub_all : forall L E S1 S2 T1 T2,
      asub E T1 S1 ->
      (forall X : atom, X `notin` L ->
          asub (E & X ~ T1) (open S2 X) (open T2 X)) ->
      asub E (typ_all S1 S2) (typ_all T1 T2).

Lemma asub_sub : forall E S T, 
  asub E S T -> judge (asub_env_to_env E) (sub S T).
Proof.
  intros E S T Asub.
  induction Asub; auto.
  Case "Asub_trans_tvar".
    eapply subtype_trans with (T2 := U).
    assert (binds X (sub X U) (asub_env_to_env E)). skip.
    eapply judge_var. eauto.
    eapply lc_sub. auto. 
    assert (lc_j (sub U T)). eapply lc_from_j. eauto.
    inversion H1. auto.
    auto.
  Case "Asub_all".
    pick fresh X and apply subtype_all. auto.
    simpl in H0.
    eapply H0 with (X := X). auto.
Qed.

(* ********************************************************************** *)
(** ** Reflexivity (1) *)

Lemma sub_reflexivity : forall E T,
  judge (asub_env_to_env E) (wf_typ T) ->
  asub E T T.
Proof with eauto.
  intros E T Wf.
  remember (wf_typ T) as J.
  remember (asub_env_to_env E) as E0.
  induction Wf; subst.
  pick fresh Y and apply sub_all...
Qed.

Lemma 
binds X (wft_typ T) (asub_env_to_env E) -> exists U, binds X U E.



(* ********************************************************************** *)
(** * #<a name="values"></a># Values *)

Inductive value : exp -> Prop :=
  | value_abs : forall T e1,
      lc (exp_abs T e1) ->
      value (exp_abs T e1)
  | value_tabs : forall T e1,
      lc (exp_tabs T e1) ->
      value (exp_tabs T e1)
.


(* ********************************************************************** *)
(** * #<a name="reduction"></a># Reduction *)

Inductive red : exp -> exp -> Prop :=
  | red_app_1 : forall e1 e1' e2,
      lc e2 ->
      red e1 e1' ->
      red (exp_app e1 e2) (exp_app e1' e2)
  | red_app_2 : forall e1 e2 e2',
      value e1 ->
      red e2 e2' ->
      red (exp_app e1 e2) (exp_app e1 e2')
  | red_tapp : forall e1 e1' V,
      lc V ->
      red e1 e1' ->
      red (exp_tapp e1 V) (exp_tapp e1' V)
  | red_abs : forall T e1 v2,
      lc (exp_abs T e1) ->
      value v2 ->
      red (exp_app (exp_abs T e1) v2) (open e1 v2)
  | red_tabs : forall T1 e1 T2,
      lc (exp_tabs T1 e1) ->
      lc T2 ->
      red (exp_tapp (exp_tabs T1 e1) T2) (open e1 T2)
.

Lemma typing_inv_abs : forall E S1 e1 T,
  ~ (exists x, exists T, binds x (typing (exp_abs S1 e1) T) E) ->
  judge E (typing (exp_abs S1 e1) T) ->
  forall U1 U2, judge E (sub T (typ_arrow U1 U2)) ->
     judge E (sub  U1 S1)
  /\ exists S2, exists L, forall X Y, X `notin` L -> Y `notin` L ->
     judge (E & X ~ typing Y S1) (typing (open e1 Y) S2) /\
     judge E (sub S2 U2).
Proof with auto.
  intros E S1 e1 T Nin Typ.
  remember (typing (exp_abs S1 e1) T) as J.
  generalize dependent T.
  induction Typ; intros T11 EQ U1 U2 Sub; inversion EQ; subst.
Case "hyp".
  unfold not in Nin.
  assert False. apply Nin; exists X; exists T11; auto. 
  auto.
  contradiction.
Case "typing_abs".
  split. skip.
Case "typing_sub".
  eapply IHTyp1 with (T := S); auto.
  eapply subtype_trans with (T2 := T11); auto.
Qed.
  


(* ********************************************************************** *)
(** ** Preservation (20) *)

Lemma preservation : forall e e' T,
  judge empty (typing e T) ->
  red e e' ->
  judge empty (typing e' T).
Proof with simpl_env; eauto.
  intros e e' T Typ. 
  remember empty as E.
  remember (typing e T) as J.
  generalize dependent e.
  generalize dependent T.
  generalize dependent e'.
  induction Typ; intros e' T11 e11 HeqJ Red; subst; 
     try solve [ inversion HeqJ];
     try solve [ inversion HeqJ; subst; inversion Red ]...
  Case "hyp".
    inversion H.
  Case "exp_app".
    inversion HeqJ; subst.
    inversion Red; subst.
    Subcase "red_app_1". eauto.
    Subcase "red_app_2". eauto.
    Subcase "red_abs".
      inversion Typ1.
      
      
  


Lemma typing_inv_abs : forall E S1 e1 T,
  judge E (typing (exp_abs S1 e1) T) ->
  forall U1 U2, judge E (sub T (typ_arrow U1 U2)) ->
     judge E (sub  U1 S1)
  /\ exists S2, exists L, forall X Y, X `notin` L -> Y `notin` L ->
     judge (E & X ~ typing Y S1) (typing (open e1 Y) S2) /\
     judge E (sub S2 U2).
Proof with auto.
  intros E S1 e1 T Typ.
  remember (typing (exp_abs S1 e1) T) as J.
  generalize dependent e1.
  generalize dependent S1.
  induction Typ; intros S11 b1 EQ U1 U2 Sub; inversion EQ; subst.
  Case "typing_abs".
    inversion Sub; subst.
    split...
    exists T1. exists L...
  Case "typing_sub".
    auto using (sub_transitivity T).
Qed.





(********************** STOP HERE ********************************************)
Lemma subord_typing_sub : 
  judge (E & X ~ typing e T & F) 


Lemma wf_typ_open : forall E U T1 T2,
  ok E ->
  wf_typ E (typ_all T1 T2) ->
  wf_typ E U ->
  wf_typ E (open T2 U).
Proof with simpl_env; eauto.
  intros E U T1 T2 Ok WA WU.
  inversion WA; subst.
  pick fresh X.
  rewrite (subst_intro X)...
  rewrite_env (E & map (subst_tb X U) empty).
  eapply  wf_typ_subst_tb...
Qed.


Lemma j_narrow : forall E F X Y Q J
  judge E (((Y, sub X Q) :: E) & F) J ->
  ok (((Y,sub X P):: E) & F) ->
  judge E (sub E P Q) ->
  judge ((Y, sub X P):: E & F) J.
Proof with simpl_env; eauto.
  intros V U T E F X Hwf_typ Hok.
  remember (E & X ~ bind_sub V & F) as K. generalize dependent E. revert F U.
  induction Hwf_typ; intros F U0 E0 Hok Heq; subst...
  Case "wf_typ_var".
    binds_cases H...
  Case "typ_all".
    pick fresh Y and apply wf_typ_all...
    rewrite_env (E0 & (X ~ bind_sub U0) & (F & Y ~ bind_sub T1)).
    apply H0...
Qed.







Definition subst_tb (Z : atom) (P : typ) (b : binding) : binding :=
  match b with
  | bind_sub T => bind_sub (subst Z P T)
  | bind_typ T => bind_typ (subst Z P T)
  end.


Inductive wf_typ : env -> typ -> Prop :=
  | wf_typ_top : forall E,
      wf_typ E typ_top
  | wf_typ_var : forall U E (X : atom),
      binds X (bind_sub U) E ->
      wf_typ E (fvar X)
  | wf_typ_arrow : forall E T1 T2,
      wf_typ E T1 ->
      wf_typ E T2 ->
      wf_typ E (typ_arrow T1 T2)
  | wf_typ_all : forall L E T1 T2,
      wf_typ E T1 ->
      (forall X : atom, X `notin` L ->
        wf_typ (E & X ~ bind_sub T1) (open T2 X)) ->
      wf_typ E (typ_all T1 T2)
.

(** An environment E is well-formed, denoted [(wf_env E)], if each atom
    is bound at most at once and if each binding is to a well-formed
    type.  This is a stronger relation than #<a
    href="Environment.html##ok">the <code>ok</code> relation</a>#
    defined in the #<a href="Environment.html">Environment</a>#
    library.  We need this relation in order to restrict the subtyping
    and typing relations, defined below, to contain only well-formed
    environments.  (This relation is missing in the original statement
    of the #<a
    href="http://alliance.seas.upenn.edu/~plclub/cgi-bin/poplmark/">POPLmark
    Challenge</a>#.)  *)

Inductive wf_env : env -> Prop :=
  | wf_env_empty :
      wf_env empty
  | wf_env_sub : forall (E : env) (X : atom) (T : typ),
      wf_env E -> wf_typ E T -> X `notin` dom E -> wf_env (E & X ~ bind_sub T)
  | wf_env_typ : forall (E : env) (x : atom) (T : typ),
      wf_env E -> wf_typ E T -> x `notin` dom E -> wf_env (E & x ~ bind_typ T).


(* ********************************************************************** *)
(** * #<a name="sub"></a># Subtyping *)

(** The definition of subtyping is straightforward.  It uses the #<a
    href="Environment.html##binds">binds</a># relation from the #<a
    href="Environment.html">Environment</a># library (in the
    [sub_trans_tvar] case) and cofinite quantification (in the
    [sub_all] case). *)

Inductive sub : env -> typ -> typ -> Prop :=
  | sub_top : forall E S,
      wf_env E ->
      wf_typ E S ->
      sub E S typ_top
  | sub_refl_tvar : forall E X,
      wf_env E ->
      wf_typ E (fvar X) ->
      sub E (fvar X) (fvar X)
  | sub_trans_tvar : forall U E T X,
      binds X (bind_sub U) E ->
      sub E U T ->
      sub E (fvar X) T
  | sub_arrow : forall E S1 S2 T1 T2,
      sub E T1 S1 ->
      sub E S2 T2 ->
      sub E (typ_arrow S1 S2) (typ_arrow T1 T2)
  | sub_all : forall L E S1 S2 T1 T2,
      sub E T1 S1 ->
      (forall X : atom, X `notin` L ->
          sub (E & X ~ bind_sub T1) (open S2 X) (open T2 X)) ->
      sub E (typ_all S1 S2) (typ_all T1 T2)
  (*IF sum*)
  | sub_sum : forall E S1 S2 T1 T2,
      sub E S1 T1 ->
      sub E S2 T2 ->
      sub E (typ_sum S1 S2) (typ_sum T1 T2)
  (*ENDIF*)
.


(* ********************************************************************** *)
(** * #<a name="typing_doc"></a># Typing *)

(** The definition of subtyping is straightforward.  It uses the #<a
    href="Environment.html##binds">binds</a># relation from the #<a
    href="Environment.html">Environment</a># library (in the
    [typing_var] case) and cofinite quantification in the cases
    involving binders (e.g., [typing_abs] and [typing_tabs]). *)

Inductive typing : env -> exp -> typ -> Prop :=
  | typing_var : forall E x T,
      wf_env E ->
      binds x (bind_typ T) E ->
      typing E (fvar x) T
  | typing_abs : forall L E V e1 T1,
      (forall x : atom, x `notin` L ->
        typing (E & x ~ bind_typ V) (open e1 x) T1) ->
      typing E (exp_abs V e1) (typ_arrow V T1)
  | typing_app : forall T1 E e1 e2 T2,
      typing E e1 (typ_arrow T1 T2) ->
      typing E e2 T1 ->
      typing E (exp_app e1 e2) T2
  | typing_tabs : forall L E V e1 T1,
      (forall X : atom, X `notin` L ->
        typing (E & X ~ bind_sub V) (open e1 X) (open T1 X)) ->
      typing E (exp_tabs V e1) (typ_all V T1)
  | typing_tapp : forall T1 E e1 T T2,
      typing E e1 (typ_all T1 T2) ->
      sub E T T1 ->
      typing E (exp_tapp e1 T) (open T2 T)
  | typing_sub : forall S E e T,
      typing E e S ->
      sub E S T ->
      typing E e T
  (*IF let*)
  | typing_let : forall L T1 T2 e1 e2 E,
      typing E e1 T1 ->
      (forall x, x `notin` L ->
        typing (E & x ~ bind_typ T1) (open e2 x) T2) ->
      typing E (exp_let e1 e2) T2
  (*ENDIF*)
  (*IF sum*)
  | typing_inl : forall T1 T2 e1 E,
      typing E e1 T1 ->
      wf_typ E T2 ->
      typing E (exp_inl e1) (typ_sum T1 T2)
  | typing_inr : forall T1 T2 e1 E,
      typing E e1 T2 ->
      wf_typ E T1 ->
      typing E (exp_inr e1) (typ_sum T1 T2)
  | typing_case : forall L T1 T2 T e1 e2 e3 E,
      typing E e1 (typ_sum T1 T2) ->
      (forall x : atom, x `notin` L ->
        typing (E & x ~ bind_typ T1) (open e2 x) T) ->
      (forall x : atom, x `notin` L ->
        typing (E & x ~ bind_typ T2) (open e3 x) T) ->
      typing E (exp_case e1 e2 e3) T
  (*ENDIF*)
.


(* ********************************************************************** *)
(** * #<a name="values"></a># Values *)

Inductive value : exp -> Prop :=
  | value_abs : forall T e1,
      lc (exp_abs T e1) ->
      value (exp_abs T e1)
  | value_tabs : forall T e1,
      lc (exp_tabs T e1) ->
      value (exp_tabs T e1)
  (*IF sum*)
  | value_inl : forall e1,
      value e1 ->
      value (exp_inl e1)
  | value_inr : forall e1,
      value e1 ->
      value (exp_inr e1)
  (*ENDIF*)
.


(* ********************************************************************** *)
(** * #<a name="reduction"></a># Reduction *)

Inductive red : exp -> exp -> Prop :=
  | red_app_1 : forall e1 e1' e2,
      lc e2 ->
      red e1 e1' ->
      red (exp_app e1 e2) (exp_app e1' e2)
  | red_app_2 : forall e1 e2 e2',
      value e1 ->
      red e2 e2' ->
      red (exp_app e1 e2) (exp_app e1 e2')
  | red_tapp : forall e1 e1' V,
      lc V ->
      red e1 e1' ->
      red (exp_tapp e1 V) (exp_tapp e1' V)
  | red_abs : forall T e1 v2,
      lc (exp_abs T e1) ->
      value v2 ->
      red (exp_app (exp_abs T e1) v2) (open e1 v2)
  | red_tabs : forall T1 e1 T2,
      lc (exp_tabs T1 e1) ->
      lc T2 ->
      red (exp_tapp (exp_tabs T1 e1) T2) (open e1 T2)
  (*IF let*)
  | red_let_1 : forall e1 e1' e2,
      red e1 e1' ->
      body_e e2 ->
      red (exp_let e1 e2) (exp_let e1' e2)
  | red_let : forall v1 e2,
      value v1 ->
      body_e e2 ->
      red (exp_let v1 e2) (open e2 v1)
  (*ENDIF*)
  (*IF sum*)
  | red_inl_1 : forall e1 e1',
      red e1 e1' ->
      red (exp_inl e1) (exp_inl e1')
  | red_inr_1 : forall e1 e1',
      red e1 e1' ->
      red (exp_inr e1) (exp_inr e1')
  | red_case_1 : forall e1 e1' e2 e3,
      red e1 e1' ->
      body_e e2 ->
      body_e e3 ->
      red (exp_case e1 e2 e3) (exp_case e1' e2 e3)
  | red_case_inl : forall v1 e2 e3,
      value v1 ->
      body_e e2 ->
      body_e e3 ->
      red (exp_case (exp_inl v1) e2 e3) (open e2 v1)
  | red_case_inr : forall v1 e2 e3,
      value v1 ->
      body_e e2 ->
      body_e e3 ->
      red (exp_case (exp_inr v1) e2 e3) (open e3 v1)
  (*ENDIF*)
.


(* ********************************************************************** *)
(** * #<a name="auto"></a># Automation *)

(** We declare most constructors as [Hint]s to be used by the [auto]
    and [eauto] tactics.  We exclude constructors from the subtyping
    and typing relations that use cofinite quantification.  It is
    unlikely that [eauto] will find an instantiation for the finite
    set [L], and in those cases, [eauto] can take some time to fail.
    (A priori, this is not obvious.  In practice, one adds as hints
    all constructors and then later removes some constructors when
    they cause proof search to take too long.) *)

Hint Constructors lc wf_typ wf_env value red.
Hint Resolve sub_top sub_refl_tvar sub_arrow.
(*IF sum*)
Hint Resolve sub_sum typing_inl typing_inr.
(*ENDIF*)
Hint Resolve typing_var typing_app typing_tapp typing_sub.
(*IF sum*)
Hint Resolve typing_inl typing_inr.
(*ENDIF*)




(* 
*** Local Variables: ***
*** coq-prog-name: "coqtop" ***
*** coq-prog-args: ("-emacs-U") ***
*** End: ***
 *)