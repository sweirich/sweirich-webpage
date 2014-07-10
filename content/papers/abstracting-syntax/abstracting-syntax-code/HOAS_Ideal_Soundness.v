(** Type-safety proofs for Fsub.

    Authors: Brian Aydemir and Arthur Charguéraud, with help from
    Aaron Bohannon, Jeffrey Vaughan, and Dimitrios Vytiniotis.

    In parentheses are given the label of the corresponding lemma in
    the appendix (informal proofs) of the POPLmark Challenge. *)

Require Export HOAS_Typed_Definitions.


(* *********************************************************************** *)
(** * Equalities concerning [senv]s *)

Lemma to_tag_subst_tb_ident : forall Z P b,
  to_tag (subst_tb Z P b) = to_tag b.
Proof.
  induction b; reflexivity.
Qed.

Hint Rewrite to_tag_subst_tb_ident : rew_env.

Lemma to_senv_map_ident : forall Z P F,
  to_senv (map (subst_tb Z P) F) = to_senv F.
Proof with auto.
  pose proof to_tag_subst_tb_ident.
  induction F as [ | (y, b) F' ]; simpl_env; simpl; try congruence 3.
Qed.

Hint Rewrite to_senv_map_ident : rew_env.


(* ********************************************************************** *)
(** * #<a name="wft"></a># Properties of [wf_typ] *)

(** NOTE: Should come "for free" from the library.

    - ok_from_wf_typ
    - type_from_wf_typ (holds by definition, now)
    - wf_typ_weakening
    - wf_typ_weakening_head
    - wf_typ_strengthening
    - wf_typ_subst_tb *)

(*
Lemma ok_from_wf_typ : forall E T,
  wf_typ E T -> ok E.
Proof.
  intros E T H; induction H; eauto.
Qed.

Lemma type_from_wf_typ : forall E T,
  wf_typ E T -> lc E T Typ.
Proof.
  intros E T H; induction H; eauto 6 using ok_from_wf_typ.
Qed.

Lemma wf_typ_weakening : forall T E F G,
  wf_typ (G ++ E) T ->
  ok (G ++ F ++ E) ->
  wf_typ (G ++ F ++ E) T.
Proof with simpl_env; eauto.
  intros T E F G Hwf_typ Hk.
  remember (G ++ E) as F.
  generalize dependent G.
  induction Hwf_typ; intros G Hok Heq; subst...
  Case "wf_typ_all".
    pick fresh Y and apply wf_typ_all...
    rewrite <- concat_assoc.
    apply H0...
Qed.

Lemma wf_typ_weaken_head : forall T E F,
  wf_typ E T ->
  ok (F ++ E) ->
  wf_typ (F ++ E) T.
Proof.
  intros.
  rewrite_env (nil ++ F++ E).
  auto using wf_typ_weakening.
Qed.

Lemma wf_typ_strengthening : forall E F x T,
 wf_typ (F ++ [(x, Exp)] ++ E) T ->
 wf_typ (F ++ E) T.
Proof with simpl_env; eauto.
  intros E F x T H.
  remember (F ++ [(x, Exp)] ++ E) as G.
  generalize dependent F.
  induction H; intros F Heq; subst...
  Case "wf_typ_var".
    binds_cases H0...
  Case "wf_typ_all".
    pick fresh Y and apply wf_typ_all...
    rewrite <- concat_assoc.
    apply H1...
Qed.

Lemma wf_typ_subst_tb : forall F E Z P T,
  wf_typ (F ++ [(Z, Typ)] ++ E) T ->
  wf_typ E P ->
  wf_typ (F ++ E) (subst_tt Z P T).
Proof with simpl_env; eauto using wf_typ_weaken_head, type_from_wf_typ.
  intros F E Z P T WT WP.
  remember (F ++ [(Z, Typ)] ++ E) as G.
  generalize dependent F.
  induction WT; intros F EQ; subst; simpl subst_tt...
  Case "wf_typ_var".
    destruct (X == Z); subst...
  Case "wf_typ_all".
    pick fresh Y and apply wf_typ_all...
    rewrite subst_tt_open_tt_var...
    rewrite <- concat_assoc.
    apply H0...
Qed.
*)

Lemma wf_typ_open : forall E U T1 T2,
  wf_typ E (typ_all T1 in T2) ->
  wf_typ E U ->
  wf_typ E (open_tt T2 U).
Proof with simpl_env; eauto.
  intros E U T1 T2 WA WU.
  inversion WA; subst.
  pick fresh X.
  rewrite (subst_tt_intro X)...
  rewrite_env (nil ++ E).
  eapply wf_typ_subst_tb...
Qed.


(* ********************************************************************** *)
(** * #<a name="oktwft"></a># Properties of [wf_env] and [wf_typ] *)

Lemma ok_from_wf_env : forall E,
  wf_env E ->
  ok E.
Proof.
  intros E H; induction H; auto.
Qed.

Hint Resolve ok_from_wf_env.

Lemma wf_typ_from_binds_sub : forall x U E,
  wf_env E ->
  binds x (bind_sub U) E ->
  wf_typ (to_senv E) U.
Proof with auto using wf_typ_weaken_head.
  induction 1; intros J; simpl; simpl_env; binds_cases J...
  inversion H4; subst...
Qed.

Lemma wf_typ_from_binds_typ : forall x U E,
  wf_env E ->
  binds x (bind_typ U) E ->
  wf_typ (to_senv E) U.
Proof with auto using wf_typ_weaken_head.
  induction 1; intros J; simpl; simpl_env; binds_cases J...
  inversion H4; subst...
Qed.

Lemma wf_typ_from_wf_env_typ : forall x T E,
  wf_env ([(x, bind_typ T)] ++ E) ->
  wf_typ (to_senv E) T.
Proof.
  intros x T E H. inversion H; auto.
Qed.

Lemma wf_typ_from_wf_env_sub : forall x T E,
  wf_env ([(x, bind_sub T)] ++ E) ->
  wf_typ (to_senv E) T.
Proof.
  intros x T E H. inversion H; auto.
Qed.


(* ********************************************************************** *)
(** * #<a name="okt"></a># Properties of [wf_env] *)

Lemma wf_env_narrowing : forall V E F U X,
  wf_env (F ++ [(X, bind_sub V)] ++ E) ->
  wf_typ (to_senv E) U ->
  wf_env (F ++ [(X, bind_sub U)] ++ E).
Proof with eauto.
  induction F; intros U X Wf_env Wf;
    inversion Wf_env; subst; simpl_env in *...
  constructor... simpl_env in *...
  constructor... simpl_env in *...
Qed.

Lemma wf_env_strengthening : forall x T E F,
  wf_env (F ++ [(x, bind_typ T)] ++ E) ->
  wf_env (F ++ E).
Proof with eauto using wf_typ_strengthening.
  induction F; intros Wf_env; inversion Wf_env; subst; simpl_env in *...
  constructor... simpl_env in *...
  constructor... simpl_env in *...
Qed.

Lemma wf_env_subst_tb : forall Q Z P E F,
  wf_env (F ++ [(Z, bind_sub Q)] ++ E) ->
  wf_typ (to_senv E) P ->
  wf_env (map (subst_tb Z P) F ++ E).
Proof with eauto using wf_typ_subst_tb.
  induction F; intros Wf_env WP; simpl_env;
    inversion Wf_env; simpl_env in *; simpl subst_tb...
  constructor... simpl_env in *...
  constructor... simpl_env in *...
Qed.


(* ********************************************************************** *)
(** * #<a name="subst"></a># Environment is unchanged by substitution for a fresh name *)

(** NOTE: Should come "for free" from the library.

    - notin_fv_tt_open
    - notin_fv_wf *)

(*
Lemma notin_fv_tt_open : forall (Y X : atom) T,
  X `notin` fv_tt (open_tt T Y) ->
  X `notin` fv_tt T.
Proof.
 intros Y X T. unfold open_tt.
 generalize 0.
 induction T; simpl; intros k Fr; notin_simpl; try apply notin_union; eauto.
Qed.

Lemma notin_fv_wf : forall E (X : atom) T,
  wf_typ (to_senv E) T ->
  X `notin` dom E ->
  X `notin` fv_tt T.
Proof with auto.
  intros E X T Wf_typ.
  remember (to_senv E) as E'.
  generalize dependent E.
  induction Wf_typ; intros F Eq Fr; subst; simpl;
    try solve [repeat apply notin_union; eapply_first_hyp; eauto]...
  Case "wf_typ_var".
    assert (X0 `in` (dom (to_senv F))). eapply binds_In; eauto.
    simpl_env in *...
  Case "wf_typ_arrow".
    repeat apply notin_union; auto; eapply_first_hyp; eauto.
  Case "wf_typ_all".
    repeat apply notin_union... eapply_first_hyp; eauto.
    pick fresh Y.
    apply (notin_fv_tt_open Y).
    apply H0 with (E := [(Y, bind_sub T2)] ++ F)...
  Case "wf_typ_sum".
    repeat apply notin_union; auto; eapply_first_hyp; eauto.
Qed.
*)

Lemma map_subst_tb_id : forall G Z P,
  wf_env G ->
  Z `notin` dom G ->
  G = map (subst_tb Z P) G.
Proof with auto.
  intros G Z P H.
  induction H; simpl; intros Fr; simpl_env...
  rewrite <- IHwf_env...
    rewrite <- subst_tt_fresh... eapply notin_fv_wf; eauto.
  rewrite <- IHwf_env...
    rewrite <- subst_tt_fresh... eapply notin_fv_wf; eauto.
Qed.


(* *********************************************************************** *)
(** * Other lemmas *)

(** NOTE: Should come "for free" from the library.

    - bind_typ_fresh
    - subst_fresh_exp_typ *)

(*
Lemma bind_typ_fresh : forall E F x V,
  wf_typ (F ++ [(x, Exp)] ++ E) V ->
  x `notin` fv V.
Proof with auto.
  intros E F x V WFT.
  remember (F ++ [(x, Exp)] ++ E) as E'.
  generalize dependent F.
  induction WFT; intros F EQ; subst; simpl;
    try solve [repeat apply notin_union; eapply_first_hyp; eauto]...
  Case "wf_typ_var".
    assert (x <> X)...
    intro; subst.
    binds_get H0.
  Case "wf_typ_arrow".
    repeat apply notin_union; auto; eapply_first_hyp; eauto.
  Case "wf_typ_all".
    repeat apply notin_union; auto.
    eapply IHWFT; eauto.
    pick fresh y.
    apply (notin_fv_tt_open y).
    apply H0 with (F0 := [(y, Typ)] ++ F)...
  Case "wf_typ_sum".
    repeat apply notin_union; auto; eapply_first_hyp; eauto.
Qed.

Lemma subst_fresh_exp_typ : forall E F x u V,
  wf_typ (F ++ [(x, Exp)] ++ E) V ->
  subst x u V = V.
Proof with auto.
  intros.
  rewrite <- subst_fresh...
  eapply bind_typ_fresh; eauto.
Qed.
*)


(* *********************************************************************** *)
(** * Facts about [wf_exp] *)

(** NOTE: Should come "for free" from the library.

    - ok_from_wf_exp
    - expr_from_wf_exp (holds by definition now)
    - wf_exp_weakening
    - wf_exp_weakening_head
    - wf_exp_subst_ee
    - wf_exp_subst_te
    - wf_exp_open_ee
    - wf_exp_open_te *)

(*
Lemma ok_from_wf_exp : forall E e,
  wf_exp E e -> ok E.
Proof.
  induction 1; eauto using ok_from_wf_typ.
Qed.

Lemma expr_from_wf_exp : forall E e,
  wf_exp E e -> lc E e Exp.
Proof.
  induction 1; eauto 8 using ok_from_wf_typ, ok_from_wf_exp, type_from_wf_typ.
Qed.

Lemma wf_exp_weakening : forall e E F G,
  wf_exp (G ++ E) e ->
  ok (G ++ F ++ E) ->
  wf_exp (G ++ F ++ E) e.
Proof with simpl_env; eauto using wf_typ_weakening.
  intros e E F G H Hk.
  remember (G ++ E) as F.
  generalize dependent G.
  induction H; intros G Hok Heq; subst...
  Case "wf_exp_abs".
    pick fresh x and apply wf_exp_abs...
    rewrite <- concat_assoc.
    apply H1...
  Case "wf_exp_tabs".
    pick fresh x and apply wf_exp_tabs...
    rewrite <- concat_assoc.
    apply H1...
  Case "wf_exp_let".
    pick fresh x and apply wf_exp_let...
    rewrite <- concat_assoc.
    apply H1...
  Case "wf_exp_case".
    pick fresh x and apply wf_exp_case...
    rewrite <- concat_assoc.
    apply H1...
    rewrite <- concat_assoc.
    apply H3...
Qed.

Lemma wf_exp_weaken_head : forall e E F,
  wf_exp E e ->
  ok (F ++ E) ->
  wf_exp (F ++ E) e.
Proof.
  intros.
  rewrite_env (nil ++ F++ E).
  auto using wf_exp_weakening.
Qed.

Lemma wf_exp_subst_ee : forall F E z g e,
  wf_exp (F ++ [(z, Exp)] ++ E) e ->
  wf_exp E g ->
  wf_exp (F ++ E) (subst_ee z g e).
Proof with simpl_env;
           eauto using wf_typ_strengthening,
                       wf_typ_subst_tb,
                       wf_exp_weaken_head,
                       expr_from_wf_exp.
  intros F E z g e H J.
  remember (F ++ [(z, Exp)] ++ E) as G.
  generalize dependent F.
  induction H; intros F EQ; subst; simpl subst_ee...
  Case "wf_exp_var".
    destruct (x == z); subst...
  Case "wf_exp_abs".
    pick fresh y and apply wf_exp_abs...
    rewrite (subst_fresh_exp_typ E F)...
    rewrite subst_ee_open_ee_var...
    rewrite <- concat_assoc.
    apply H1...
  Case "wf_exp_tabs".
    pick fresh y and apply wf_exp_tabs...
    rewrite (subst_fresh_exp_typ E F)...
    rewrite subst_ee_open_te_var...
    rewrite <- concat_assoc.
    apply H1...
  Case "wf_exp_tapp".
    rewrite (subst_fresh_exp_typ E F z g T)...
  Case "wf_exp_let".
    pick fresh y and apply wf_exp_let...
    rewrite subst_ee_open_ee_var...
    rewrite <- concat_assoc.
    apply H1...
  Case "wf_exp_case".
    pick fresh y and apply wf_exp_case...
    rewrite subst_ee_open_ee_var...
    rewrite <- concat_assoc.
    apply H1...
    rewrite subst_ee_open_ee_var...
    rewrite <- concat_assoc.
    apply H3...
Qed.

Lemma wf_exp_subst_te : forall F E Z T e,
  wf_exp (F ++ [(Z, Typ)] ++ E) e ->
  wf_typ E T ->
  wf_exp (F ++ E) (subst_te Z T e).
Proof with simpl_env;
           eauto using wf_typ_strengthening,
                       wf_typ_subst_tb,
                       type_from_wf_typ,
                       wf_exp_weaken_head,
                       expr_from_wf_exp.
  intros F E Z T e H J.
  remember (F ++ [(Z, Typ)] ++ E) as G.
  generalize dependent F.
  induction H; intros F EQ; subst; simpl subst_te...
  Case "wf_exp_var".
    destruct (x == Z); subst...
    binds_get H0.
  Case "wf_exp_abs".
    pick fresh y and apply wf_exp_abs...
    rewrite subst_te_open_ee_var...
    rewrite <- concat_assoc.
    apply H1...
  Case "wf_exp_tabs".
    pick fresh y and apply wf_exp_tabs...
    rewrite subst_te_open_te_var...
    rewrite <- concat_assoc.
    apply H1...
  Case "wf_exp_let".
    pick fresh y and apply wf_exp_let...
    rewrite subst_te_open_ee_var...
    rewrite <- concat_assoc.
    apply H1...
  Case "wf_exp_case".
    pick fresh y and apply wf_exp_case...
    rewrite subst_te_open_ee_var...
    rewrite <- concat_assoc.
    apply H1...
    rewrite subst_te_open_ee_var...
    rewrite <- concat_assoc.
    apply H3...
Qed.

Lemma wf_exp_open_ee : forall L E e v,
  (forall x : atom, x `notin` L -> wf_exp ([(x,Exp)] ++ E) (open_ee e x)) ->
  wf_exp E v ->
  wf_exp E (open_ee e v).
Proof with simpl_env; auto.
  intros L E e v H J.
  pick fresh x.
  rewrite (subst_ee_intro x)...
  rewrite_env (nil ++ E).
  eapply wf_exp_subst_ee...
Qed.

Lemma wf_exp_open_te : forall L E e V,
  (forall X : atom, X `notin` L -> wf_exp ([(X,Typ)] ++ E) (open_te e X)) ->
  wf_typ E V ->
  wf_exp E (open_te e V).
Proof with simpl_env; auto.
  intros L E e V H J.
  pick fresh X.
  rewrite (subst_te_intro X)...
  rewrite_env (nil ++ E).
  eapply wf_exp_subst_te...
Qed.
*)


(* ********************************************************************** *)
(** * #<a name="regularity"></a># Regularity of relations *)

Lemma sub_regular : forall E S T,
  sub E S T ->
  wf_env E /\ wf_typ (to_senv E) S /\ wf_typ (to_senv E) T.
Proof with simpl_env; intuition.
  intros E S T H.
  induction H...
  Case "sub_all".
    repeat split...
    SCase "Second of original three conjuncts".
      pick fresh Y and apply wf_typ_all...
      destruct (H1 Y)...
    SCase "Third of original three conjuncts".
      pick fresh Y and apply wf_typ_all...
      destruct (H1 Y)...
Qed.

Lemma typing_regular : forall E e T,
  typing E e T ->
  wf_env E /\ wf_exp (to_senv E) e /\ wf_typ (to_senv E) T.
Proof with simpl_env; try solve [intuition].
  intros E e T H; induction H...
  Case "typing_var".
    repeat split...
    eauto using wf_typ_from_binds_typ.
  Case "typing_abs".
    pick fresh y.
    destruct (H0 y) as [Hok [J K]]...
    repeat split. inversion Hok...
    SCase "Second of original three conjuncts".
      pick fresh x and apply wf_exp_abs.
        eauto using type_from_wf_typ, wf_typ_from_wf_env_typ.
        destruct (H0 x)...
    SCase "Third of original three conjuncts".
      apply wf_typ_arrow; eauto using wf_typ_from_wf_env_typ.
      simpl in *; simpl_env in *.
      rewrite_env (nil ++ to_senv E).
      eapply wf_typ_strengthening; simpl_env; eauto.
  Case "typing_app".
    repeat split...
    destruct IHtyping1 as [_ [_ K]].
    inversion K...
  Case "typing_tabs".
    pick fresh Y.
    destruct (H0 Y) as [Hok [J K]]...
    inversion Hok; subst.
    repeat split...
    SCase "Second of original three conjuncts".
      pick fresh X and apply wf_exp_tabs.
        eauto using type_from_wf_typ, wf_typ_from_wf_env_sub...
        destruct (H0 X)...
    SCase "Third of original three conjuncts".
      pick fresh Z and apply wf_typ_all...
      destruct (H0 Z)...
  Case "typing_tapp".
    destruct (sub_regular _ _ _ H0) as [R1 [R2 R3]].
    repeat split...
    SCase "Third of original three conjuncts".
      destruct IHtyping as [R1' [R2' R3']].
      eapply wf_typ_open; eauto.
  Case "typing_sub".
    repeat split...
    destruct (sub_regular _ _ _ H0)...
  Case "typing_let".
    repeat split...
    SCase "Second of original three conjuncts".
      pick fresh y and apply wf_exp_let...
      destruct (H1 y) as [K1 [K2 K3]]...
    SCase "Third of original three conjuncts".
      pick fresh y.
      destruct (H1 y) as [K1 [K2 K3]]...
      simpl in *; simpl_env in *.
      rewrite_env (nil ++ to_senv E).
      eapply wf_typ_strengthening; simpl_env; eauto.
  Case "typing_case".
    repeat split...
    SCase "Second of original three conjuncts".
      pick fresh x and apply wf_exp_case...
        destruct (H1 x) as [? [? ?]]...
        destruct (H3 x) as [? [? ?]]...
    SCase "Third of original three conjuncts".
      pick fresh y.
      destruct (H1 y) as [K1 [K2 K3]]...
      simpl in *; simpl_env in *.
      rewrite_env (nil ++ to_senv E).
      eapply wf_typ_strengthening; simpl_env; eauto.
Qed.

Lemma value_regular : forall e,
  value e ->
  exists E, wf_exp E e.
Proof.
  intros e H.
  induction H; eauto.
  destruct IHvalue; eauto.
  destruct IHvalue; eauto.
Qed.

Lemma red_regular_l : forall e e',
  red e e' ->
  exists E, wf_exp E e.
Proof with eauto.
  intros e e' H.
  induction H...
  destruct IHred...
  destruct IHred...
Qed.

Lemma red_regular_r : forall E e e',
  red e e' ->
  wf_exp E e ->
  wf_exp E e'.
Proof with eauto using wf_exp_open_ee, wf_exp_open_te.
  intros E e e' H.
  induction H; intros J; inversion J; subst; eauto.
  Case "red_abs".
    inversion H4...
  Case "red_tabs".
    inversion H3...
  Case "red_let".
    inversion J...
  Case "red_case_inl".
    inversion H5...
  Case "red_case_inr".
    inversion H5...
Qed.

Lemma red_regular : forall e e',
  red e e' ->
  exists E, wf_exp E e /\ wf_exp E e'.
Proof.
  intros e e' H.
  destruct (red_regular_l _ _ H) as [E' J].
  exists E'.
  eauto using red_regular_r.
Qed.


(* *********************************************************************** *)
(** * #<a name="auto"></a># Automation *)

Hint Extern 1 (wf_env ?E) =>
  match goal with
  | H: sub _ _ _ |- _ => apply (proj1 (sub_regular _ _ _ H))
  | H: typing _ _ _ |- _ => apply (proj1 (typing_regular _ _ _ H))
  end.

Hint Extern 1 (wf_typ (to_senv ?E) ?T) =>
  match goal with
  | H: typing E _ T |- _ => apply (proj2 (proj2 (typing_regular _ _ _ H)))
  | H: sub E T _ |- _ => apply (proj1 (proj2 (sub_regular _ _ _ H)))
  | H: sub E _ T |- _ => apply (proj2 (proj2 (sub_regular _ _ _ H)))
  end.

Hint Extern 1 (lc _ ?T Typ) =>
  let go E := (apply (type_from_wf_typ (to_senv E))) in
  match goal with
  | H: typing ?E _ T |- _ => go E
  | H: sub ?E T _ |- _ => go E
  | H: sub ?E _ T |- _ => go E
  end.

Hint Extern 1 (lc _ ?e Exp) =>
  match goal with
  | H: typing _ ?e _ |- _ =>
      apply (expr_from_wf_exp _ _ (proj1 (proj2 (typing_regular _ _ _ H))))
  end.

Hint Extern 1 (wf_exp _ ?e) =>
  match goal with
    | H : typing _ e _ |- _ =>
      apply (proj1 (proj2 (typing_regular _ _ _ H)))
  end.


(* ********************************************************************** *)
(** * #<a name="subtyping"></a># Properties of subtyping *)


(* ********************************************************************** *)
(** ** Reflexivity (1) *)

Lemma sub_reflexivity : forall E T,
  wf_env E ->
  wf_typ (to_senv E) T ->
  sub E T T.
Proof with auto.
  intros E T Ok Wf.
  remember (to_senv E) as E'.
  generalize dependent E.
  induction Wf; intros F Ok Eq; subst; auto.
  Case "sub_all".
    pick fresh Y and apply sub_all...
Qed.


(* ********************************************************************** *)
(** ** Weakening (2) *)

Section Weakening.

Hint Extern 1 (wf_typ _ _) =>
  repeat rewrite <- map_concat.

Hint Extern 1 (ok _) =>
  repeat rewrite <- map_concat.

Lemma sub_weakening : forall E F G S T,
  sub (G ++ E) S T ->
  wf_env (G ++ F ++ E) ->
  sub (G ++ F ++ E) S T.
Proof with simpl_env; auto using wf_typ_weakening.
  intros E F G S T Sub Ok.
  remember (G ++ E) as H.
  generalize dependent G.
  induction Sub; intros G Ok EQ; subst...
  Case "sub_top".
    constructor...
  Case "sub_refl_tvar".
    constructor...
  Case "sub_trans_tvar".
    apply (sub_trans_tvar U)...
  Case "sub_all".
    pick fresh Y and apply sub_all...
    rewrite <- concat_assoc.
    apply H0...
    constructor...
Qed.

End Weakening.


(* ********************************************************************** *)
(** ** Narrowing and transitivity (3) *)

Section Narrowing_and_transitivity.

Hint Extern 1 (wf_typ _ ?S) =>
  match goal with
    | H : wf_typ _ S |- _ =>
      simpl_env in H; simpl in H; simpl_env in H
  end.

Lemma sub_narrowing_aux : forall Q F E Z P S T,
  (forall E S T, sub E S Q -> sub E Q T -> sub E S T) ->
  sub (F ++ [(Z, bind_sub Q)] ++ E) S T ->
  sub E P Q ->
  sub (F ++ [(Z, bind_sub P)] ++ E) S T.
Proof with simpl_env; eauto using wf_env_narrowing.
  intros Q F E Z P S T TransQ SsubT PsubQ.
  remember (F ++ [(Z, bind_sub Q)] ++ E) as G. generalize dependent F.
  induction SsubT; intros F EQ; subst...
  Case "sub_top".
    constructor...
  Case "sub_refl_tvar".
    constructor...
  Case "sub_trans_tvar".
    destruct (X == Z); subst.
    SCase "X = Z".
      apply (sub_trans_tvar P); [ eauto using fresh_mid_head | ].
      apply TransQ.
      SSCase "P <: Q".
        rewrite_env (empty ++ (F ++ [(Z, bind_sub P)]) ++ E).
        apply sub_weakening...
      SSCase "Q <: T".
        binds_get H.
        inversion H1; subst...
    SCase "X <> Z".
      apply (sub_trans_tvar U)...
  Case "sub_all".
    pick fresh Y and apply sub_all...
    rewrite <- concat_assoc.
    apply H0...
Qed.

Lemma sub_transitivity_aux : forall E' Q E S T,
  wf_typ E' Q ->
  sub E S Q ->
  sub E Q T ->
  sub E S T.
Proof with simpl_env; auto.
  intros E' Q E S T W SsubQ QsubT.
  generalize dependent T.
  generalize dependent S.
  generalize dependent E.
  remember Q as Q' in |-. generalize dependent Q'.
  induction W;
    intros Q' EQ E'' S SsubQ;
    induction SsubQ; try discriminate; inversion EQ; subst;
    intros T QsubT;
    inversion QsubT; subst; eauto 4 using sub_trans_tvar.
  Case "sub_all / sub_top".
    assert (sub E0 (typ_all S1 in S2) (typ_all T1 in T2)).
      SCase "proof of assertion".
      pick fresh y and apply sub_all...
    auto.
  Case "sub_all / sub_all".
    pick fresh Y and apply sub_all.
    SCase "bounds".
      eauto.
    SCase "bodies".
      lapply (H0 Y); [ intros K | auto ].
      apply (K (open_tt T2 Y))...
      rewrite_env (empty ++ [(Y, bind_sub T0)] ++ E0).
      apply (sub_narrowing_aux T1)...
      auto using (IHW T1).
Qed.

Lemma sub_narrowing : forall Q E F Z P S T,
  sub E P Q ->
  sub (F ++ [(Z, bind_sub Q)] ++ E) S T ->
  sub (F ++ [(Z, bind_sub P)] ++ E) S T.
Proof.
  intros.
  eapply sub_narrowing_aux; eauto.
  intros.
  apply sub_transitivity_aux with (E' := to_senv E0) (Q := Q); auto.
Qed.

Lemma sub_transitivity : forall Q E S T,
  sub E S Q ->
  sub E Q T ->
  sub E S T.
Proof.
  intros.
  apply sub_transitivity_aux with (E' := to_senv E) (Q := Q); auto.
Qed.

End Narrowing_and_transitivity.


(* ********************************************************************** *)
(** ** Type substitution preserves subtyping (10) *)

Lemma sub_through_subst_tt : forall Q E F Z S T P,
  sub (F ++ [(Z, bind_sub Q)] ++ E) S T ->
  sub E P Q ->
  sub (map (subst_tb Z P) F ++ E) (subst_tt Z P S) (subst_tt Z P T).
Proof with
      simpl_env;
      eauto using wf_typ_subst_tb, wf_env_subst_tb, wf_typ_weaken_head,
                  ok_remove_mid, ok_from_wf_typ.
  intros Q E F Z S T P SsubT PsubQ.
  remember (F ++ [(Z, bind_sub Q)] ++ E) as G.
  generalize dependent F.
  induction SsubT; intros G EQ; subst; simpl subst_tt...
  Case "sub_top".
    constructor; simpl_env in *...
  Case "sub_refl_tvar".
    destruct (X == Z); subst.
    SCase "X = Z".
      apply sub_reflexivity; simpl_env in *...
    SCase "X <> Z".
      apply sub_reflexivity; simpl_env in *...
      inversion H0; subst...
  Case "sub_trans_tvar".
    destruct (X == Z); subst.
    SCase "X = Z".
      apply (sub_transitivity Q).
      SSCase "left branch".
        rewrite_env (empty ++ map (subst_tb Z P) G ++ E).
        apply sub_weakening...
      SSCase "right branch".
        rewrite (subst_tt_fresh Z P Q).
          binds_get H.
            inversion H1; subst...
          apply (notin_fv_wf E); eauto using fresh_mid_tail.
    SCase "X <> Z".
      apply (sub_trans_tvar (subst_tt Z P U))...
      rewrite (map_subst_tb_id E Z P);
        [ | auto | eapply fresh_mid_tail; eauto ].
      binds_cases H...
  Case "sub_all".
    pick fresh X and apply sub_all...
    assert (lc (to_senv E) P Typ)...
    rewrite subst_tt_open_tt_var...
    rewrite subst_tt_open_tt_var...
    rewrite_env (map (subst_tb Z P) ([(X, bind_sub T1)] ++ G) ++ E).
    apply H0...
Qed.


(* ********************************************************************** *)
(** * #<a name="typing"></a># Properties of typing *)


(* ********************************************************************** *)
(** ** Weakening (5) *)

Section Typing_weakening.

Hint Extern 4 (wf_typ _ _) =>
  apply wf_typ_weakening; repeat rewrite <- map_concat.

Lemma typing_weakening : forall E F G e T,
  typing (G ++ E) e T ->
  wf_env (G ++ F ++ E) ->
  typing (G ++ F ++ E) e T.
Proof with simpl_env;
           eauto using wf_typ_from_wf_env_typ,
                       wf_typ_from_wf_env_sub,
                       sub_weakening.
  intros E F G e T Typ.
  remember (G ++ E) as H.
  generalize dependent G.
  induction Typ; intros G EQ Ok; subst; auto...
  Case "typing_abs".
    pick fresh x and apply typing_abs.
    lapply (H x); [intros K | auto].
    rewrite <- concat_assoc.
    apply (H0 x)...
    constructor...
  Case "typing_tabs".
    pick fresh X and apply typing_tabs.
    lapply (H X); [intros K | auto].
    rewrite <- concat_assoc.
    apply (H0 X)...
    constructor...
  Case "typing_let".
    pick fresh x and apply typing_let...
    lapply (H0 x); [intros K | auto].
    rewrite <- concat_assoc.
    apply H0...
    constructor...
  Case "typing_inl".
    constructor...
  Case "typing_inr".
    constructor...
  Case "typing_case".
    pick fresh x and apply typing_case...
    SCase "inl branch".
      lapply (H0 x); [intros K | auto].
      rewrite <- concat_assoc.
      apply H0...
      assert (J : wf_typ (to_senv (G ++ F ++ E)) (typ_sum T1 T2))...
      inversion J...
    SCase "inr branch".
      lapply (H2 x); [intros K | auto].
      rewrite <- concat_assoc.
      apply H2...
      assert (J : wf_typ (to_senv (G ++ F ++ E)) (typ_sum T1 T2))...
      inversion J...
Qed.

End Typing_weakening.


(* ********************************************************************** *)
(** ** Strengthening (6) *)

Lemma sub_strengthening : forall x U E F S T,
  sub (F ++ [(x, bind_typ U)] ++ E) S T ->
  sub (F ++ E) S T.
Proof with simpl_env;
           eauto using wf_typ_strengthening, wf_env_strengthening.
  intros x U E F S T SsubT.
  remember (F ++ [(x, bind_typ U)] ++ E) as E'.
  generalize dependent F.
  induction SsubT; intros F EQ; subst...
  Case "sub_top".
    constructor; simpl_env in *...
  Case "sub_refl_tvar".
    constructor; simpl_env in *...
  Case "sub_trans_tvar".
    apply (sub_trans_tvar U0)...
    binds_cases H...
  Case "sub_all".
    pick fresh X and apply sub_all...
    rewrite <- concat_assoc.
    apply H0...
Qed.


(************************************************************************ *)
(** ** Narrowing for typing (7) *)

Lemma typing_narrowing : forall Q E F X P e T,
  sub E P Q ->
  typing (F ++ [(X, bind_sub Q)] ++ E) e T ->
  typing (F ++ [(X, bind_sub P)] ++ E) e T.
Proof with simpl_env; eauto using wf_env_narrowing, sub_narrowing.
  intros Q E F X P e T PsubQ Typ.
  remember (F ++ [(X, bind_sub Q)] ++ E) as E'.
  generalize dependent F.
  induction Typ; intros F EQ; subst...
  Case "typing_var".
    binds_cases H0...
  Case "typing_abs".
    pick fresh y and apply typing_abs.
    rewrite <- concat_assoc.
    apply H0...
  Case "typing_tabs".
    pick fresh Y and apply typing_tabs.
    rewrite <- concat_assoc.
    apply H0...
  Case "typing_let".
    pick fresh y and apply typing_let...
    rewrite <- concat_assoc.
    apply H0...
  Case "typing_inl".
    constructor; simpl_env in *...
  Case "typing_inr".
    constructor; simpl_env in *...
  Case "typing_case".
    pick fresh y and apply typing_case...
    SCase "inl branch".
      rewrite <- concat_assoc.
      apply H0...
    SCase "inr branch".
      rewrite <- concat_assoc.
      apply H2...
Qed.


(************************************************************************ *)
(** ** Substitution preserves typing (8) *)

Lemma typing_through_subst_ee : forall U E F x T e u,
  typing (F ++ [(x, bind_typ U)] ++ E) e T ->
  typing E u U ->
  typing (F ++ E) (subst_ee x u e) T.
Proof with simpl_env;
           eauto using wf_typ_strengthening,
                       wf_env_strengthening,
                       sub_strengthening.
  intros U E F x T e u TypT TypU.
  remember (F ++ [(x, bind_typ U)] ++ E) as E'.
  generalize dependent F.
  assert (TypT' := TypT).
  assert (J : lc (to_senv E) u Exp)...
  induction TypT; intros F EQ; subst; simpl subst_ee...
  Case "typing_var".
    destruct (x0 == x); subst.
    SCase "x0 = x".
      binds_get H0.
        inversion H2; subst.
        rewrite_env (empty ++ F ++ E).
        apply typing_weakening...
    SCase "x0 <> x".
      binds_cases H0.
        eauto using wf_env_strengthening.
        eauto using wf_env_strengthening.
  Case "typing_abs".
    rewrite (subst_fresh_exp_typ (to_senv E) (to_senv F))...
    pick fresh y and apply typing_abs.
    rewrite subst_ee_open_ee_var...
    rewrite <- concat_assoc.
    apply H0...
    assert (WfT := proj2 (proj2 (typing_regular _ _ _ TypT'))).
    simpl_env in WfT; simpl in WfT; simpl_env in WfT.
    inversion WfT; subst...
  Case "typing_tabs".
    rewrite (subst_fresh_exp_typ (to_senv E) (to_senv F) x u V)...
    pick fresh Y and apply typing_tabs.
    rewrite subst_ee_open_te_var...
    rewrite <- concat_assoc.
    apply H0...
    assert (WfT := proj2 (proj2 (typing_regular _ _ _ TypT'))).
    simpl_env in WfT; simpl in WfT; simpl_env in WfT.
    inversion WfT; subst...
  Case "typing_tapp".
    rewrite (subst_fresh_exp_typ (to_senv E) (to_senv F) x u T)...
    assert (WfT := proj1 (proj2 (sub_regular _ _ _ H))).
    simpl_env in WfT; simpl in WfT; simpl_env in WfT...
  Case "typing_let".
    pick fresh y and apply typing_let...
    rewrite subst_ee_open_ee_var...
    rewrite <- concat_assoc.
    apply H0...
  Case "typing_inl".
    constructor; simpl_env in *...
  Case "typing_inr".
    constructor; simpl_env in *...
  Case "typing_case".
    pick fresh y and apply typing_case...
      rewrite subst_ee_open_ee_var...
        rewrite <- concat_assoc.
        apply H0...
      rewrite subst_ee_open_ee_var...
        rewrite <- concat_assoc.
        apply H2...
Qed.


(************************************************************************ *)
(** ** Type substitution preserves typing (11) *)

Lemma typing_through_subst_te : forall Q E F Z e T P,
  typing (F ++ [(Z, bind_sub Q)] ++ E) e T ->
  sub E P Q ->
  typing (map (subst_tb Z P) F ++ E) (subst_te Z P e) (subst_tt Z P T).
Proof with simpl_env;
           eauto using wf_env_subst_tb,
                       wf_typ_subst_tb,
                        sub_through_subst_tt.
  intros Q E F Z e T P Typ' PsubQ.
  assert (J : lc (to_senv E) P Typ)...
  remember (F ++ [(Z, bind_sub Q)] ++ E) as G.
  generalize dependent F.
  induction Typ'; intros F EQ; subst;
    simpl subst_te in *; simpl subst_tt in *...
  Case "typing_var".
    assert (x <> Z).
      intro; subst.
      binds_get H0.
    destruct (x == Z); try solve [ intuition ].
    apply typing_var...
      rewrite (map_subst_tb_id E Z P);
        [ | auto | eapply fresh_mid_tail; eauto ].
      binds_cases H0...
  Case "typing_abs".
    pick fresh y and apply typing_abs.
    rewrite subst_te_open_ee_var...
    rewrite_env (map (subst_tb Z P) ([(y, bind_typ V)] ++ F) ++ E).
    apply H0...
  Case "typing_tabs".
    pick fresh Y and apply typing_tabs.
    rewrite subst_te_open_te_var...
    rewrite subst_tt_open_tt_var...
    rewrite_env (map (subst_tb Z P) ([(Y, bind_sub V)] ++ F) ++ E).
    apply H0...
  Case "typing_tapp".
    rewrite subst_tt_open_tt...
  Case "typing_let".
    pick fresh y and apply typing_let...
    rewrite subst_te_open_ee_var...
    rewrite_env (map (subst_tb Z P) ([(y, bind_typ T1)] ++ F) ++ E).
    apply H0...
  Case "typing_inl".
    constructor; simpl_env in *...
  Case "typing_inr".
    constructor; simpl_env in *...
  Case "typing_case".
    pick fresh y and apply typing_case...
    SCase "inl branch".
      rewrite subst_te_open_ee_var...
      rewrite_env (map (subst_tb Z P) ([(y, bind_typ T1)] ++ F) ++ E).
      apply H0...
    SCase "inr branch".
      rewrite subst_te_open_ee_var...
      rewrite_env (map (subst_tb Z P) ([(y, bind_typ T2)] ++ F) ++ E).
      apply H2...
Qed.



(* ********************************************************************** *)
(** * #<a name="preservation"></a># Preservation *)


(* ********************************************************************** *)
(** ** Inversion of typing (13) *)

Lemma typing_inv_abs : forall E S1 e1 T,
  typing E (exp_abs S1 in e1) T ->
  forall U1 U2, sub E T (typ_arrow U1 U2) ->
     sub E U1 S1
  /\ exists S2, exists L, forall x, x `notin` L ->
     typing ([(x, bind_typ S1)] ++ E) (open_ee e1 x) S2 /\ sub E S2 U2.
Proof with auto.
  intros E S1 e1 T Typ.
  remember (exp_abs S1 in e1) as e.
  generalize dependent e1.
  generalize dependent S1.
  induction Typ; intros S1 b1 EQ U1 U2 Sub; inversion EQ; subst.
  Case "typing_abs".
    inversion Sub; subst.
    split...
    exists T1. exists L...
  Case "typing_sub".
    auto using (sub_transitivity T).
Qed.

Lemma typing_inv_tabs : forall E S1 e1 T,
  typing E (exp_tabs S1 in e1) T ->
  forall U1 U2, sub E T (typ_all U1 in U2) ->
     sub E U1 S1
  /\ exists S2, exists L, forall X, X `notin` L ->
     typing ([(X, bind_sub U1)] ++ E) (open_te e1 X) (open_tt S2 X)
     /\ sub ([(X, bind_sub U1)] ++ E) (open_tt S2 X) (open_tt U2 X).
Proof with simpl_env; auto.
  intros E S1 e1 T Typ.
  remember (exp_tabs S1 in e1) as e.
  generalize dependent e1.
  generalize dependent S1.
  induction Typ; intros S1 e0 EQ U1 U2 Sub; inversion EQ; subst.
  Case "typing_tabs".
    inversion Sub; subst.
    split...
    exists T1.
    exists (L0 `union` L).
    intros Y Fr.
    split...
    rewrite_env (empty ++ [(Y, bind_sub U1)] ++ E).
    apply (typing_narrowing S1)...
  Case "typing_sub".
    auto using (sub_transitivity T).
Qed.

Lemma typing_inv_inl : forall E e1 T,
  typing E (exp_inl e1) T ->
  forall U1 U2, sub E T (typ_sum U1 U2) ->
  exists S1, typing E e1 S1 /\ sub E S1 U1.
Proof with eauto.
  intros E e1 T Typ.
  remember (exp_inl e1) as e. generalize dependent e1.
  induction Typ; intros e' EQ U1 U2 Sub; inversion EQ; subst.
  Case "typing_sub".
    eauto using (sub_transitivity T).
  Case "typing_inl".
    inversion Sub; subst...
Qed.

Lemma typing_inv_inr : forall E e1 T,
  typing E (exp_inr e1) T ->
  forall U1 U2, sub E T (typ_sum U1 U2) ->
  exists S1, typing E e1 S1 /\ sub E S1 U2.
Proof with eauto.
  intros E e1 T Typ.
  remember (exp_inr e1) as e. generalize dependent e1.
  induction Typ; intros e' EQ U1 U2 Sub; inversion EQ; subst.
  Case "typing_sub".
    eauto using (sub_transitivity T).
  Case "typing_inr".
    inversion Sub; subst...
Qed.


(* ********************************************************************** *)
(** ** Preservation (20) *)

Lemma preservation : forall E e e' T,
  typing E e T ->
  red e e' ->
  typing E e' T.
Proof with simpl_env; eauto.
  intros E e e' T Typ'. generalize dependent e'.
  induction Typ'; intros e' Red; try solve [ inversion Red; subst; eauto ].
  Case "typing_app".
    inversion Red; subst...
    SCase "red_abs".
      destruct (typing_inv_abs _ _ _ _ Typ'1 T1 T2) as [P1 [S2 [L P2]]].
        apply sub_reflexivity...
      pick fresh x.
      destruct (P2 x) as [? ?]...
      rewrite (subst_ee_intro x)...
      rewrite_env (empty ++ E).
      apply (typing_through_subst_ee T).
        apply (typing_sub S2)...
          rewrite_env (empty ++ [(x, bind_typ T)] ++ E).
          apply sub_weakening...
        eauto.
  Case "typing_tapp".
    inversion Red; subst...
    SCase "red_tabs".
      destruct (typing_inv_tabs _ _ _ _ Typ' T1 T2) as [P1 [S2 [L P2]]].
        apply sub_reflexivity...
      pick fresh X.
      destruct (P2 X) as [? ?]...
      rewrite (subst_te_intro X T2 T)...
      rewrite (subst_tt_intro X e0 T)...
      rewrite_env (map (subst_tb X T) empty ++ E).
      apply (typing_through_subst_te T1)...
  Case "typing_let".
    inversion Red; subst.
      SCase "red_let_1".
        eapply typing_let; eauto.
      SCase "red_let".
        pick fresh x.
        rewrite (subst_ee_intro x)...
        rewrite_env (empty ++ E).
        apply (typing_through_subst_ee T1)...
  Case "typing_case".
    inversion Red; subst.
    SCase "red_case_1".
      eapply typing_case; eauto.
    SCase "red_case_inl".
      destruct (typing_inv_inl _ _ _ Typ' T1 T2) as [S1 [J2 J3]].
        apply sub_reflexivity...
      pick fresh x.
      rewrite (subst_ee_intro x)...
      rewrite_env (empty ++ E).
      apply (typing_through_subst_ee T1)...
    SCase "red_case_inr".
      destruct (typing_inv_inr _ _ _ Typ' T1 T2) as [S1 [J2 J3]].
        apply sub_reflexivity...
      pick fresh x.
      rewrite (subst_ee_intro x)...
      rewrite_env (empty ++ E).
      apply (typing_through_subst_ee T2)...
Qed.


(* ********************************************************************** *)
(** * #<a name="progress"></a># Progress *)


(* ********************************************************************** *)
(** ** Canonical forms (14) *)

Lemma canonical_form_abs : forall e U1 U2,
  value e ->
  typing empty e (typ_arrow U1 U2) ->
  exists V, exists e1, e = exp_abs V in e1.
Proof.
  intros e U1 U2 Val Typ.
  remember empty as E.
  remember (typ_arrow U1 U2) as T.
  revert U1 U2 HeqT HeqE.
  induction Typ; intros U1 U2 EQT EQE; subst;
    try solve [ inversion Val | inversion EQT | eauto ].
  Case "typing_sub".
    inversion H; subst; eauto.
    inversion H0.
Qed.

Lemma canonical_form_tabs : forall e U1 U2,
  value e ->
  typing empty e (typ_all U1 in U2) ->
  exists V, exists e1, e = exp_tabs V in e1.
Proof.
  intros e U1 U2 Val Typ.
  remember empty as E.
  remember (typ_all U1 in U2) as T.
  revert U1 U2 HeqT HeqT.
  induction Typ; intros U1 U2 EQT EQE; subst;
    try solve [ inversion Val | inversion EQT | eauto ].
  Case "typing_sub".
    inversion H; subst; eauto.
    inversion H0.
Qed.

Lemma canonical_form_sum : forall e T1 T2,
  value e -> typing empty e (typ_sum T1 T2) ->
  exists e1, e = exp_inl e1 \/ e = exp_inr e1.
Proof.
  intros e T1 T2 Val Typ.
  remember empty as E.
  remember (typ_sum T1 T2) as T.
  revert T1 T2 HeqE HeqT.
  induction Typ; intros U1 U2 EQE EQT; subst;
    try solve [ inversion Val | inversion EQT | eauto ].
  Case "typing_sub".
    inversion H; subst; eauto.
    inversion H0.
Qed.


(* ********************************************************************** *)
(** ** Progress (16) *)

Lemma progress : forall e T,
  typing empty e T ->
  value e \/ exists e', red e e'.
Proof with eauto.
  intros e T Typ.
  remember empty as E. generalize dependent HeqE.
  assert (Typ' : typing E e T)...
  assert (Wf : wf_exp (to_senv E) e)...
  induction Typ; intros EQ; subst...
  Case "typing_var".
    inversion H0.
  Case "typing_app".
    apply or_intror.
    destruct IHTyp1 as [Val1 | [e1' Rede1']]...
    SCase "Val1".
      destruct IHTyp2 as [Val2 | [e2' Rede2']]...
      SSCase "Val2".
        destruct (canonical_form_abs _ _ _ Val1 Typ1) as [S [e3 EQ]].
        subst.
        exists (open_ee e3 e2)...
  Case "typing_tapp".
    apply or_intror.
    destruct IHTyp as [Val1 | [e1' Rede1']]...
    SCase "Val1".
      destruct (canonical_form_tabs _ _ _ Val1 Typ) as [S [e3 EQ]].
      subst.
      exists (open_te e3 T)...
  Case "typing_let".
    apply or_intror.
    destruct IHTyp as [Val1 | [e1' Rede1']]...
  Case "typing_inl".
    destruct (typing_inv_inl _ _ _ Typ' T1 T2) as [S1 [J2 J3]].
    apply sub_reflexivity...
    destruct IHTyp as [J1 | [e' J1]]...
  Case "typing_inr".
    destruct (typing_inv_inr _ _ _ Typ' T1 T2) as [S1 [J2 J3]].
    apply sub_reflexivity...
    destruct IHTyp as [J1 | [e' J1]]...
  Case "typing_case".
    apply or_intror.
    destruct IHTyp as [Val1 | [e' Rede']]...
    SCase "Val1".
      destruct (canonical_form_sum _ _ _ Val1 Typ) as [e4 [J1 | J1]].
      SSCase "Left J1".
        subst.
        exists (open_ee e2 e4).
        inversion Val1; subst...
      SSCase "Right J1".
        subst.
        exists (open_ee e3 e4)...
        inversion Val1; subst...
Qed.
