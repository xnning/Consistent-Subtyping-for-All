From TLC Require Import LibLN.
Require Import DeclDef DeclInfra DeclProp.
Require Import Translation.
Require Import PBCDef PBCInfra PBCProp.
Require Import DeclTyping DeclSub DeclEnvSub.
Require Import OLDef.

(** * Conservative Extension *)

Hint Constructors dtyping otyping.
Hint Resolve denv_static_dokt otyping_regular.

Lemma conservative_extension: forall E e T,
    denv_static E ->
    dterm_static e ->
    dtyp_static T ->
    otyping E e T ->
    exists A, dtyping E e A /\ dsub E A T.
Proof.
  introv Hen Htm Htyp.

  introv Ht.
  inductions Ht; autos ~;
     try(solve[exists~ T; splits~]).

  exists ~ T. splits~. apply~ dsub_refl.
  apply* dwft_from_env_has_typ.

  exists ~ (dtyp_nat).

  pick_fresh y.
  forwards ~ : H1 y.
  constructor~. inversions~ Htyp.
  forwards ~ : H0 y.
  lets ~ [? [? ?]]: otyping_regular H2.
  apply denv_static_dokt in H3.
  apply* dokt_push_typ_inv.
  forwards ~ : H0 y.
  lets ~ [? [? ?]]: otyping_regular H2.
  forwards ~ : H0 y.
  lets ~ [? [? [? ?]]]: otyping_regular H2.
  destruct H2 as (C & [? ?]).
  apply dtyping_dtyping' in H2.
  assert (dtyping' E (dtrm_absann A e) (dtyp_arrow A C)).
  apply dtyping'_absann with y; auto.
  lets [_ [? _]]: dsub_regular H3.
  assert (dwft E C).
  apply_empty~ dwft_strengthen_typ.
  assert (y \notin dfv_tt C).
  apply (dwft_notin_env H6); auto.
  auto.
  lets ~ : dtyping'_dtyping H4.
  exists ~ (dtyp_arrow A C). splits~. constructor~.
  apply* dsub_refl.
  apply_empty* dsub_strengthen_typ.

  pick_fresh y.
  forwards ~ : H1 y.
  constructor~. inversions~ Htyp.
  forwards ~ : H0 y.
  lets ~ [? [? ?]]: otyping_regular H2.
  apply denv_static_dokt in H3.
  apply* dokt_push_typ_inv.
  forwards ~ : H0 y.
  lets ~ [? [? ?]]: otyping_regular H2.
  forwards ~ : H0 y.
  lets ~ [? [? [? ?]]]: otyping_regular H2.
  destruct H2 as (C & [? ?]).
  apply dtyping_dtyping' in H2.
  assert (dtyping' E (dtrm_abs e) (dtyp_arrow A C)).
  apply dtyping'_abs with y; auto.
  lets [_ [? _]]: dsub_regular H3.
  assert (dwft E C).
  apply_empty~ dwft_strengthen_typ.
  assert (y \notin dfv_tt C).
  apply (dwft_notin_env H6); auto.
  auto.
  lets ~ : dtyping'_dtyping H4.
  exists ~ (dtyp_arrow A C). splits~. constructor~.
  apply* dsub_refl.
  apply_empty* dsub_strengthen_typ.

  forwards ~ (B1 & [? ?]) : IHHt1.
    lets~ [? [? [? ?]]] : otyping_regular Ht1.
    lets~ [? [? [? ?]]] : otyping_regular Ht1.
  forwards ~ (B2 & [? ?]) : IHHt2.
    lets~ [? [? [? ?]]] : otyping_regular Ht2.
    lets~ [? [? [? ?]]] : otyping_regular Ht2.
  forwards ~ (C1 & C2 & [? ?]): dsub_match_arrow H0.
  inversions H4.
  exists ~ C2. splits~.
  apply* dtyping_app.
  apply dsub_consub.
  apply dsub_trans with A1; auto.

  forwards ~ (A0 & [? ?]) : IHHt.
  lets~ [? [? [? ?]]] : otyping_regular Ht.
  exists ~ A0. splits~.
  apply dsub_trans with A; auto.

  inversions Htyp.
  pick_fresh y.
  forwards ~ : H0 y.
  destruct H1 as (C & [? ?]).
  apply dtyping_dtyping' in H1.
  assert (dtyping' E e (dtyp_all (dclose_tt y C))).
  apply dtyping'_gen with y; auto.
  assert (y \notin dfv_tt (dclose_tt y C)).
    apply dclose_tt_fresh.
  auto.
  rewrite~ <- dclose_tt_open_var.
  lets~ [_ [? _]]: dsub_regular H3.
  exists ~ (dtyp_all (dclose_tt y C)).
  splits~.
  apply* dtyping'_dtyping.
  apply dsub'_dsub.
  apply dsub'_allR with y; auto.
  assert (y \notin dfv_tt (dtyp_all (dclose_tt y C))).
  simpls. apply dclose_tt_fresh.
  auto.
  apply dsub'_allL with (dtyp_fvar y); auto.
  rewrite~ <- dclose_tt_open_var.
  apply~ dsub_dsub'.
  lets~ [? [? _]]: dsub_regular H3.

  inversions Htm.
  apply otyping_regular in Ht. destructs Ht.
  forwards ~ : IHHt. destruct H7 as (A0 & [I1 I2]).
  pick_fresh y.
  forwards ~ (C & [? ?]) : H0 y. clear H0 IHHt.
  assert (I3 : dsub (E & y ~: A) A0 A).
    apply~ dsub_push.
  lets ~ (T & [? ?]) : dtyping_bind_strengthen H7 I3.
  exists T. splits~.
  apply dtyping'_dtyping.
  apply dtyping'_let with y A0; auto.
  apply~ dtyping_dtyping'.
  apply~ dtyping_dtyping'.
  apply dsub_strengthen_typ_push in H9.
  apply dsub_strengthen_typ_push in H8.
  lets~ : dsub_trans H9 H8.
Qed.

Lemma conserv_extension_b: forall E e T,
    denv_static E ->
    dterm_static e ->
    dtyp_static T ->
    dtyping E e T ->
    otyping E e T.
Proof.
  introv Hen Htm Htyp.

  introv Ht.
  inductions Ht; autos ~.

  inversions Htyp.
  inversions Htm.
  apply_fresh otyping_absann as x; auto.
  apply~ H1.
  apply~ denv_static_typ.
  forwards ~ : H0 x.
  lets ~ [? [_ _]]: dtyping_regular H2.
  apply dokt_push_typ_inv in H3. auto.

  inversions~ Htm.
  forwards ~ : IHHt1.
  apply* dtyping_static_preserve.
  forwards ~ : IHHt2.
  apply* dtyping_static_preserve.
  apply* otyping_app.
  apply otyping_sub with A; auto.
  apply dsub_trans with (dtyp_arrow A1 A2); auto.
  apply~ dmatch_static_sub.
  apply* dtyping_static_preserve.
  constructor~.
  apply~ dconsub_static_sub.
  apply* dtyping_static_preserve.
  lets ~ [? ?] : dmatch_static_preserve H.
  apply* dtyping_static_preserve.
  apply~ dsub_refl.
  lets~ [? ?] : dmatch_regular H.

  inversions Htyp.
  inversions Htm.
  apply_fresh otyping_abs as x; auto.
  apply~ H1.
  constructor~.
  forwards ~ : H0 x.
  lets ~ [? [_ _]]: dtyping_regular H2.
  apply dokt_push_typ_inv in H6. auto.

  inversions Htyp.
  apply_fresh otyping_gen as x; auto.

  inversions Htm.
  apply_fresh otyping_let as x; auto.
  apply~ IHHt.
  apply* dtyping_static_preserve.
  apply~ H0.
  constructor~.
  apply* dtyping_static_preserve.
Qed.

(** * Monotonicity w.r.t. precision *)

Lemma monotonicity_precision': forall E F e s A,
    dtyping E e A ->
    denv_less_precise F E ->
    dterm_less_precise s e ->
    exists B, dtyping' F s B /\ dtyp_less_precise B A.
Proof.
  introv ty. gen F s.
  inductions ty; introv less_env less_tm.

  (* var *)
  inversions less_tm.
  forwards ~ (B & [? ?]) : denv_less_precise_binds H0 less_env.
  exists B. splits~.
  constructor~.
  apply* denv_less_precise_dokt_l.

  (* nat *)
  inversions less_tm.
  exists ~ dtyp_nat. splits~. constructor~. apply* denv_less_precise_dokt_l.

  (* absann *)
  inversions~ less_tm.
  pick_fresh y.
  assert (I1: denv_less_precise (F & y ~: A1) (E & y ~: A)). constructor~.
    apply dwft_denv_less_precise with E; auto.
    apply dwft_dtyp_less_precise with A; auto.
    forwards ~ : H0 y.
    lets ~ [? _] : dtyping_regular H2.
    apply* dokt_push_typ_inv.
    forwards ~ : H0 y.
    lets ~ [? _] : dtyping_regular H2.
    apply* dokt_push_typ_inv.
  assert (I2: dterm_less_precise (e1 dopen_ee_var y) (e dopen_ee_var y)). auto.
  forwards ~ (C & [? ?]) : H1 I1 I2.
  exists (dtyp_arrow A1 C). split~.
  apply dtyping'_absann with y; auto.
  apply dwft_dtyp_less_precise with A; auto.

  (* app *)
  inversions less_tm.
  forwards ~ (B & [? ?]): IHty1 less_env H4. clear IHty1.
  forwards ~ (C & [? ?]): IHty2 less_env H5. clear IHty2.
  forwards ~ (B1 & B2 & [? [? ?]]) : dmatch_less_precise_input H H2.
  exists ~ B2. splits~.
  apply dtyping'_app with (A:= B) (A1:= B1) (A3:=C); auto.
  lets ~ : dmatch_denv_less_precise H7 less_env.
  lets ~ : dconsub_dtyp_less_precise H0 H6 H8.
  lets ~ : dconsub_denv_less_precise H10 less_env.

  (* abs *)
  inversions~ less_tm.
  pick_fresh y.
  assert (I1: denv_less_precise (F & y ~: A) (E & y ~: A)). constructor~.
    apply dtyp_less_precise_refl.
    apply~ dtyp_mono_dtype.
    apply dwft_denv_less_precise with E; auto.
    forwards ~ : H0 y.
    lets ~ [? _] : dtyping_regular H2.
    apply* dokt_push_typ_inv.
    forwards ~ : H0 y.
    lets ~ [? _] : dtyping_regular H2.
    apply* dokt_push_typ_inv.
  assert (I2: dterm_less_precise (e1 dopen_ee_var y) (e dopen_ee_var y)). auto.
  forwards ~ (C & [? ?]) : H1 I1 I2.
  exists (dtyp_arrow A C). split~.
  apply dtyping'_abs with y; auto.
  assert (dwft F C).
    lets : dtyping'_dtyping H2.
    lets [_ [_ ?]] : dtyping_regular H5.
    apply_empty* dwft_strengthen_typ.
  assert (y \notin dfv_tt C).
    apply (dwft_notin_env H5); auto.
  auto.
  constructor~.
    apply dtyp_less_precise_refl.
    apply~ dtyp_mono_dtype.

  (* gen *)
  pick_fresh y.
  assert (I1: denv_less_precise (F & y ~tvar ) (E & y ~tvar)). constructor~.
  forwards ~ (C & [? ?]) : H0 I1 less_tm.
  exists (dtyp_all (dclose_tt y C)). split~.
  apply dtyping'_gen with y; auto.
  assert (y \notin dfv_tt (dclose_tt y C)).
    apply dclose_tt_fresh; auto.
  auto.
  rewrite~ <- dclose_tt_open_var.
    lets : dtyping'_dtyping H1.
    lets [_ [_ ?]] : dtyping_regular H4.
    auto.
    apply dtyp_less_precise'_precise.
    apply dtyp_less_precise'_all with y.
      assert (y \notin dfv_tt (dclose_tt y C)).
        apply dclose_tt_fresh; auto.
      auto.
  rewrite~ <- dclose_tt_open_var.
  apply~ dtyp_less_precise_precise'.
    lets : dtyping'_dtyping H1.
    lets [_ [_ ?]] : dtyping_regular H3.
    auto.

  (* let *)
  inversions~ less_tm.
  pick_fresh y.
  forwards ~ (D & [I1 I2]) : IHty less_env H4.
  assert (I3: denv_less_precise (F & y ~: D) (E & y ~: A)) by constructor~.
  assert (I4: dterm_less_precise (e4 dopen_ee_var y) (e2 dopen_ee_var y))
         by auto.
  forwards ~ (C & [? ?]) : H0 I3 I4.
  clear H0 IHty.
  exists C. split~.
  apply dtyping'_let with y D; auto.
Qed.

Lemma monotonicity_precision: forall E F e s A,
    dtyping E e A ->
    denv_less_precise F E ->
    dterm_less_precise s e ->
    exists B, dtyping F s B /\ dtyp_less_precise B A.
Proof.
  intros.
  forwards ~ (B & [? ?]): monotonicity_precision' H H0 H1.
  exists~ B. splits~.
  apply* dtyping'_dtyping.
Qed.

(** * Monotonicity of cast insertion *)

Lemma monotonicity_cast_insertion': forall E F e1 e2 s1 A,
    d2ptyping E e1 A s1 ->
    denv_less_precise F E ->
    dterm_less_precise e2 e1 ->
    exists s2 B, d2ptyping' F e2 B s2 /\
    dtyp_less_precise' B A /\
    pterm_less_precise s2 s1.
Proof.
  introv ty1. gen F e2.
  inductions ty1; introv less_env less_tm.

  (* var *)
  forwards ~ (C & [? ?]) : denv_less_precise_binds H0 less_env.
  inversions less_tm.
  exists (ptrm_fvar x) C. splits~.
  constructor~.
  lets~ : denv_less_precise_dokt_l less_env.
  apply* dtyp_less_precise_precise'.
  apply* pterm_less_precise_var.
  lets~ : denv_less_precise_dokt_l less_env.

  (* nat *)
  inversions less_tm.
  exists (ptrm_nat i) dtyp_nat. splits~.
  constructor~.

  (* absann *)
  inversions~ less_tm.
  pick_fresh y.
  forwards~ : H6 y. clear H6.
  forwards~ (s2 & B0 & [? [? ?]]): H1 y (F & y ~: A1) H2.
  constructor~.
  apply dwft_denv_less_precise with E; auto.
  apply dwft_dtyp_less_precise with A; auto.
  forwards~ : H0 y.
  lets~ [? [? ?]]: d2ptyping_regular H3.
  apply* dokt_push_typ_inv.
  forwards~ : H0 y.
  lets~ [? [? ?]]: d2ptyping_regular H3.
  apply* dokt_push_typ_inv.
  exists ~ (ptrm_absann A1 (pclose_ee y s2)) (dtyp_arrow A1 B0).
  splits~.
  apply d2ptyping'_absann with y; auto.
  apply dwft_dtyp_less_precise with A; auto.
  assert (y \notin pfv_ee (pclose_ee y s2)).
    apply pclose_ee_fresh.
  auto.
  rewrite~ <- pclose_ee_open.
  lets ~ : d2ptyping'_d2ptyping H3.
  lets ~ : d2ptyping_term H7.
  constructor~.
  apply~ dtyp_less_precise_precise'.
  apply pterm_less_precise_absann with y; auto.
  assert (y \notin pfv_ee (pclose_ee y s2)).
    apply pclose_ee_fresh.
  auto.
  rewrite~ <- pclose_ee_open.
  lets ~ : d2ptyping'_d2ptyping H3.
  lets ~ : d2ptyping_term H7.

  (* app *)
  inversions less_tm.
  forwards ~ (s3 & C1 & [? [? ?]]) : IHty1_1 less_env H4.
  forwards ~ (s4 & C2 & [? [? ?]]) : IHty1_2 less_env H5.
  clear IHty1_1 IHty1_2.
  lets : dtyp_less_precise'_precise H2.
  forwards ~ (D1 & D2 & [? [? ?]]) : dmatch_less_precise_input H H9.
  lets : dmatch_denv_less_precise H10 less_env. clear H10.
  exists~ (ptrm_app (ptrm_cast C1 (dtyp_arrow D1 D2) s3)
               (ptrm_cast C2 D1 s4))
   D2.
  splits~.
  apply~ d2ptyping'_app.
  lets I1 : dtyp_less_precise'_precise H7.
  lets~ : dconsub_dtyp_less_precise H0 I1 H11.
  lets~ : dconsub_denv_less_precise H10 less_env.
  apply* dtyp_less_precise_precise'.
  apply~ pterm_less_precise_app.
  apply~ pterm_less_precise_cast.
  apply~ pterm_less_precise_cast.
  apply* dtyp_less_precise'_precise.

  (* abs *)
  inversions~ less_tm.
  pick_fresh y.
  forwards~ : H4 y. clear H4.
  forwards~ (s2 & B0 & [? [? ?]]): H1 y (F & y ~: A) H2.
  constructor~.
  apply~ dtyp_less_precise_refl.
    forwards~ : H0 y.
    lets~ [? [? ?]]: d2ptyping_regular H3.
    apply dokt_push_typ_inv in H4. auto.
  apply dwft_denv_less_precise with E; auto.
  forwards~ : H0 y.
  lets~ [? [? ?]]: d2ptyping_regular H3.
  apply* dokt_push_typ_inv.
  forwards~ : H0 y.
  lets~ [? [? ?]]: d2ptyping_regular H3.
  apply* dokt_push_typ_inv.
  exists ~ (ptrm_absann A (pclose_ee y s2)) (dtyp_arrow A B0).
  splits~.
  apply d2ptyping'_abs with y; auto.
  assert (y \notin pfv_ee (pclose_ee y s2)).
    apply pclose_ee_fresh.
  auto.
  rewrite~ <- pclose_ee_open.
  lets ~ : d2ptyping'_d2ptyping H3.
  lets ~ : d2ptyping_term H6.
  constructor~.
  apply~ dtyp_less_precise'_refl.
    forwards~ : H0 y.
    lets~ [? [? ?]]: d2ptyping_regular H6.
    apply dokt_push_typ_inv in H7. auto.
  apply pterm_less_precise_absann with y; auto.
  assert (y \notin pfv_ee (pclose_ee y s2)).
    apply pclose_ee_fresh.
  auto.
  apply* dtyp_less_precise'_precise.
  rewrite~ <- pclose_ee_open.
  lets ~ : d2ptyping'_d2ptyping H3.
  lets ~ : d2ptyping_term H6.

  (* all *)
  pick_fresh y.
  forwards~ : H y. clear H.
  forwards~ (s2 & B0 & [? [? ?]]): H0 y (F & y ~tvar) less_tm.
  constructor~.
  exists ~ (ptrm_tabs (pclose_te y s2)) (dtyp_all (dclose_tt y B0)).
  splits~.
  apply d2ptyping'_gen with y; auto.
  assert (y \notin dfv_tt (dclose_tt y B0)).
    apply dclose_tt_fresh.
  assert (y \notin pfv_te (pclose_te y s2)).
    apply pclose_te_fresh.
  auto.
  rewrite~ <- dclose_tt_open_var.
  rewrite~ <- pclose_te_open.
  lets ~ : d2ptyping'_d2ptyping H.
  lets ~ : d2ptyping_term H4.
  lets ~ : d2ptyping'_d2ptyping H.
  lets ~ [_ [_ ?]]: d2ptyping_regular H4.
  apply dtyp_less_precise'_all with y.
    assert (y \notin dfv_tt (dclose_tt y B0)).
      apply dclose_tt_fresh.
    auto.
  rewrite~ <- dclose_tt_open_var.
    lets ~ : d2ptyping'_d2ptyping H.
    lets ~ [_ [_ ?]]: d2ptyping_regular H4.
  apply pterm_less_precise_tabs with y.
  assert (y \notin pfv_te (pclose_te y s2)).
    apply pclose_te_fresh.
  auto.
  rewrite~ <- pclose_te_open.
  lets ~ : d2ptyping'_d2ptyping H.
  lets ~ : d2ptyping_term H4.

  (* let *)
  inversions~ less_tm.
  pick_fresh y.
  forwards~ : H5 y. clear H5.
  forwards ~ (s4 & C0 & [I1 [I2 I3]]) : IHty1 less_env H4.
  forwards~ (s3 & B0 & [I4 [I5 I6]]): H0 y (F & y ~: C0) H1.
  constructor~.
  apply~ dtyp_less_precise'_precise.
  clear IHty1 H0.
  exists (ptrm_app (ptrm_absann C0 (pclose_ee y s3)) (s4)) B0.
  splits~.
  apply d2ptyping'_let with y; auto.
  assert (y \notin pfv_ee (pclose_ee y s3)).
    apply pclose_ee_fresh.
  auto.
  rewrite~ <- pclose_ee_open.
  lets ~ : d2ptyping'_regular I4. destructs~ H0.
  apply~ pterm_less_precise_app.
  apply pterm_less_precise_absann with y; auto.
  assert (y \notin pfv_ee (pclose_ee y s3)).
    apply pclose_ee_fresh.
  assert (y \notin dfv_tt C0).
    apply dwft_notin_env with F; auto.
  auto.
  apply~ dtyp_less_precise'_precise.
  rewrite~ <- pclose_ee_open.
  lets ~ : d2ptyping'_regular I4. destructs~ H0.
Qed.

Lemma monotonicity_cast_insertion: forall E F e1 e2 s1 A,
    d2ptyping E e1 A s1 ->
    denv_less_precise F E ->
    dterm_less_precise e2 e1 ->
    exists s2 B, d2ptyping F e2 B s2 /\
    dtyp_less_precise B A /\
    pterm_less_precise s2 s1.
Proof.
  introv H1 H2 H3.
  forwards ~ (s2 & B & [? [? ?]]): monotonicity_cast_insertion' H1 H2 H3.
  exists ~ s2 B.
  splits~.
  apply* d2ptyping'_d2ptyping.
  apply* dtyp_less_precise'_precise.
Qed.
