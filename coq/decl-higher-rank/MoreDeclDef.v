Set Implicit Arguments.

From TLC Require Import LibLN.
Implicit Types x : var.
Require Import DeclDef.
Require Import DeclInfra.
Require Import DeclProp.
Require Import DeclTyping.
Require Import DeclSub.
Require Import DeclEnvSub.

(** Matching *)
Inductive mdmatch : denv -> dtyp -> dtyp -> dtyp -> Prop :=
  | mdmatch_arrow : forall E A1 A2,
      mdmatch E (dtyp_arrow A1 A2) A1 A2
  | mdmatch_unknown : forall E,
      mdmatch E dtyp_unknown dtyp_unknown dtyp_unknown
.

Inductive mdtyping : denv -> dtrm -> dtyp -> Prop :=
  | mdtyping_var : forall E x T,
      dokt E ->
      binds x (dbind_typ T) E ->
      mdtyping E (dtrm_fvar x) T
  | mdtyping_nat : forall E i,
      dokt E ->
      mdtyping E (dtrm_nat i) (dtyp_nat)
  | mdtyping_absann : forall L E A B e,
      dwft empty A -> (* type annotations are closed *)
      (forall x, x \notin L ->
            mdtyping (E & x ~: A) (e dopen_ee_var x) B) ->
      mdtyping E (dtrm_absann A e) (dtyp_arrow A B)
  | mdtyping_sub : forall E e A B,
      mdtyping E e A ->
      dsub E A B ->
      mdtyping E e B
  | mdtyping_app : forall E e1 e2 A A1 A2 A3,
      mdtyping E e1 A ->
      mdmatch E A A1 A2 ->
      mdtyping E e2 A3 ->
      dconsist A1 A3 ->
      mdtyping E (dtrm_app e1 e2) A2
  | mdtyping_abs : forall L E A B e,
      dtyp_mono A ->
      (forall x, x \notin L ->
            mdtyping (E & x ~: A) (e dopen_ee_var x) B) ->
      mdtyping E (dtrm_abs e) (dtyp_arrow A B)
  | mdtyping_gen : forall L E A e,
      (forall a, a \notin L ->
            mdtyping (E & a ~tvar) e (A dopen_tt_var a)) ->
      mdtyping E e (dtyp_all A)
  | mdtyping_let : forall L E A B e1 e2,
      mdtyping E e1 A ->
      (forall x, x \notin L -> 
            mdtyping (E & x ~: A) (e2 dopen_ee_var x) B) ->
      mdtyping E (dtrm_let e1 e2) B
.

Lemma mdmatch_regular : forall E A A1 A2,
    dwft E A ->
    mdmatch E A A1 A2 ->
    dwft E A1 /\ dwft E A2.
Proof.
  induction 2; eauto.
  inversions~ H.
Qed.

Lemma mdtyping_regular : forall E e T,
  mdtyping E e T -> dokt E /\ dterm e /\ dwft E T.
Proof.
  induction 1; try(solve[auto;splits~]).
  splits~. apply* dwft_from_env_has_typ.
  splits~.
    pick_fresh y. specializes H1 y. destructs~ H1.
      forwards*: dokt_push_inv.
    apply_fresh dterm_absann as y.
      pick_fresh y. specializes H1 y. destructs~ H1.
        specializes H1 y. destructs~ H1.
    apply~ dwft_arrow.
      pick_fresh y. specializes H1 y. destructs~ H1.
      apply* dokt_push_typ_inv.
      pick_fresh y. specializes H1 y. destructs~ H1.
      apply* dwft_strengthen_push.

  destructs IHmdtyping.
  splits~.

  destructs IHmdtyping1.
  destructs IHmdtyping2.
  splits~.
  apply (proj22 (mdmatch_regular H5 H0)).

  splits~.
    pick_fresh y. specializes H1 y. destructs~ H1.
      forwards*: dokt_push_inv.
    apply_fresh dterm_abs as y.
      specializes H1 y. destructs~ H1.
    apply~ dwft_arrow.
      pick_fresh y. specializes H1 y. destructs~ H1.
      apply* dokt_push_typ_inv.
      pick_fresh y. specializes H1 y. destructs~ H1.
      apply* dwft_strengthen_push.

  splits~.
    pick_fresh y. specializes H0 y. destructs~ H0.
      forwards*: dokt_push_inv.
    pick_fresh y. specializes H0 y. destructs~ H0.
    apply_fresh dwft_all as y.
      specializes H0 y. destructs~ H0.

  destructs IHmdtyping.
  splits~.
    apply_fresh dterm_let as x; auto.
      specializes H1 x. destructs~ H1.
    pick_fresh y. specializes H1 y. destructs~ H1.
      apply* dwft_strengthen_push.
Qed.

(** Automation *)

Hint Extern 1 (dokt ?E) =>
  match goal with
  | H: mdtyping _ _ _ |- _ => apply (proj31 (mdtyping_regular H))
  end.

Hint Extern 1 (dterm ?E) =>
  match goal with
  | H: mdtyping _ _ _ |- _ => apply (proj32 (mdtyping_regular H))
  end.

Hint Extern 1 (dwft ?E ?t) =>
  match goal with
  | H: mdtyping _ _ _ |- _ => apply (proj33 (mdtyping_regular H))
  end.

Hint Constructors mdmatch mdtyping dtyping.

(** Complete *)

Lemma dtyping_mdtyping : forall E e A,
    dtyping E e A ->
    mdtyping E e A.
Proof.
  introv ty. induction ty; auto.
  apply_fresh mdtyping_absann as x; auto.

  lets~ : dmatch_arrow H.
  lets~ (C & D & [? [? ?]]) : dconsub_prop1 H0.
  assert (I1: mdtyping E e2 C).
    apply mdtyping_sub with A3; auto.
  destruct H1 as [sub | un].
    assert (I2: mdtyping E e1 (dtyp_arrow D A2)).
      apply mdtyping_sub with A; auto.
      apply dsub_trans with (dtyp_arrow A1 A2); auto.
      constructor~. apply~ dsub_refl.
      apply dmatch_regular in H; auto.
      destruct H; auto.
      apply mdtyping_app with (A:=dtyp_arrow D A2) (A1:=D) (A2:=A2) (A3:=C); auto.
   destruct un as [un1 [un2 un3]].
   assert (I2: mdtyping E e1 dtyp_unknown).
     apply mdtyping_sub with A; auto.
     apply~ dtyp_unknown_like_dsub_l.
     apply mdtyping_sub with dtyp_unknown; auto.
     eapply mdtyping_app with (A:=dtyp_unknown) (A1:=dtyp_unknown)
                              (A2:=dtyp_unknown) (A3:=C) ; auto.
     apply~ dtyp_unknown_like_dsub_r.

  apply_fresh mdtyping_abs as x; auto.

  apply_fresh mdtyping_gen as x; auto.

  apply_fresh mdtyping_let as x; auto. auto.
Qed.

(** Sound *)

Lemma mdmatch_dmatch : forall E A A1 A2,
    mdmatch E A A1 A2 ->
    dmatch E A A1 A2.
Proof.
  induction 1; constructor~.
Qed.

Lemma mdtyping_dtyping : forall E e A,
    mdtyping E e A ->
    exists B,
      dtyping E e B /\ dsub E B A.
Proof.
  introv ty. inductions ty.

  exists T. splits~.
  apply~ dsub_refl.
  apply* dwft_from_env_has_typ.

  exists dtyp_nat. splits~.

  pick_fresh x.
  forwards~ (C & [? ?]): H1 x.
  exists (dtyp_arrow A C). splits~.
  apply_fresh dtyping_absann as y; auto.
  apply dtyping_rename with x; auto.
  constructor~.
  apply~ dsub_refl.
  lets [? _] : dtyping_regular H2.
  apply (proj21 (dokt_push_inv H4)).
  lets [? _] : dsub_regular H3.
  apply* dokt_push_typ_inv.
  apply_empty* dsub_strengthen_typ.

  destruct IHty as (C & [? ?]).
  exists C. splits~.
  apply dsub_trans with A; auto.

  destruct IHty1 as (B1 & [? ?]).
  destruct IHty2 as (B2 & [? ?]).
  inversions H.
    apply dsub_match_arrow in H2.
    destruct H2 as (C2 & C3 & [? ?]). inversions H2.
    exists C3. splits~.
    apply dtyping_app with (A:=B1) (A1:=C2) (A3:=B2); auto.
    apply dconsub_prop2 with (C:=A3) (D:=A1); auto.

    apply dsub_unknown_r in H2.
    apply unknown_like_match with (E:=E) in H2.
    destruct H2 as (B & [? ?]).
    exists B. splits~.
    apply dtyping_app with (A:=B1) (A1:=dtyp_unknown) (A3:=B2); auto.
    apply~ dtyp_unknown_like_dsub_l.
    apply dtyping_regular in H3. destructs~ H3.

  pick_fresh x.
  forwards ~ (C & [? ?]): H1 x. clear H1.
  exists (dtyp_arrow A C). splits~.
  apply_fresh dtyping_abs as x; auto.
  apply dtyping_rename with x; auto.
  constructor~.
  apply~ dsub_refl.
  lets [? _] : dtyping_regular H2.
  apply (proj21 (dokt_push_inv H1)).
  lets [? _] : dsub_regular H3.
  apply* dokt_push_typ_inv.
  apply_empty* dsub_strengthen_typ.

  pick_fresh x.
  forwards ~ (C & [? ?]): H0 x. clear H0.
  exists (dtyp_all (dclose_tt x C)). splits~.
  apply_fresh dtyping_gen as y; auto.
  assert (I1:x \notin dfv_tt (dclose_tt x C)).
    apply dclose_tt_fresh.
  assert (I2:y \notin dfv_tt (dclose_tt x C)).
    apply~ dnotin_fv_tt_close_inv.
  apply dtyping_rename_tvar with x; auto.
  rewrite~  <- dclose_tt_open_var.
  lets~ [_ [_ ?]]: dtyping_regular H1.
  apply_fresh dsub_allR as y.
  apply dsub_allL with (dtyp_fvar y); auto.
  apply~ dwft_var. constructor~.
  lets [? _]: dtyping_regular H1.
  apply dokt_push_inv in H0.
  destructs~ H0.
  assert (x \notin dfv_tt (dclose_tt x C)).
    apply dclose_tt_fresh.
  assert (y \notin dfv_tt (dclose_tt x C)).
    apply~ dnotin_fv_tt_close_inv.
  apply dsub_rename with x; auto.
  rewrite~ <- dclose_tt_open_var.
  lets~ [_ [_ ?]]: dtyping_regular H1.

  forwards~ (C1 & [I1 I2]): IHty. clear IHty.
  pick_fresh x.
  forwards~ (C2 & [I3 I4]): H0 x. clear H0.
  assert (I5 : dsub (E & x ~:A) C1 A).
    apply~ dsub_push.
  lets (C3 & [I6 I7]): dtyping_bind_strengthen I3 I5.
  exists C3. splits~.
  apply_fresh dtyping_let as y; auto.
  exact I1.
  apply dtyping_rename with x; auto.
  apply dsub_strengthen_typ_push in I7.
  apply dsub_strengthen_typ_push in I4.
  apply dsub_trans with C2; eauto.
Qed.