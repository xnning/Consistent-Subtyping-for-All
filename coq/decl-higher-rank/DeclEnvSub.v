Set Implicit Arguments.
Require Import TLC.LibLN.
Require Import DeclDef DeclInfra DeclProp.
Require Import DeclTyping DeclSub.

(** * ENV SUBTYPING *)

Inductive denv_sub : denv -> denv -> Prop :=
  | denv_sub_refl: forall E,
      dokt E ->
      denv_sub E E
  | denv_sub_typ: forall E F x A1 A2,
      denv_sub E F ->
      dsub E A1 A2 ->
      x # E -> x # F ->
      denv_sub (E & x ~: A1) (F & x ~: A2)
  | denv_sub_tvar: forall E F x,
      denv_sub E F ->
      x # E -> x # F ->
      denv_sub (E & x ~tvar) (F & x ~tvar)
.

Hint Constructors denv_sub.

Lemma denv_sub_dokt : forall E F,
    dokt E ->
    denv_sub F E ->
    dokt F.
Proof.
  introv oke sub. generalize dependent F.
  inductions oke; introv sub.
  inversions~ sub.
  false empty_push_inv. symmetry. exact H.
  inversions~ sub. constructor~.
  apply eq_push_inv in H0. destructs H0. substs.
  apply IHoke; auto.
  inversions~ sub. constructor~.
  apply eq_push_inv in H1. destructs H1. substs.
  apply IHoke; auto.
Qed.

Lemma denv_sub_ok : forall E F,
    ok E ->
    denv_sub F E ->
    ok F.
Proof.
  introv oke sub. generalize dependent F.
  inductions oke; introv sub.
  inversions~ sub.
  false empty_push_inv. symmetry. exact H.
  inversions~ sub. constructor~.
  apply eq_push_inv in H0. destructs H0. substs.
  apply IHoke; auto.
Qed.

Hint Resolve denv_sub_dokt denv_sub_ok.

Lemma denv_sub_binds_typ : forall E F x A,
    denv_sub F E ->
    binds x (dbind_typ A) E ->
    exists B, binds x (dbind_typ B) F /\ dsub F B A.
Proof.
  introv sub bd. inductions sub.
  exists A; splits~.
  apply~ dsub_refl.
  apply* dwft_from_env_has_typ.

  apply binds_push_inv in bd.
  destruct bd as [[I1 I2] | [I3 I4]].
  inversions I2.
  exists A1. splits~.
  apply* dsub_push.

  forwards (B & [I1 I2]) : IHsub I4.
  exists B; splits~.
  apply* dsub_push.

  apply binds_push_inv in bd.
  destruct bd as [[I1 I2] | [I3 I4]].
  inversions I2.

  forwards (B & [I1 I2]) : IHsub I4.
  exists B; splits~.
  apply* dsub_push.
Qed.

Lemma denv_sub_binds_tvar : forall E F x,
    denv_sub F E ->
    binds x (dbind_tvar) E ->
    binds x (dbind_tvar) F.
Proof.
  introv sub bd. inductions sub.
  auto.

  apply binds_push_inv in bd.
  destruct bd as [[I1 I2] | [I3 I4]].
  inversions I2.

  forwards I1 : IHsub I4.
  apply~ binds_concat_left.

  apply binds_push_inv in bd.
  destruct bd as [[I1 I2] | [I3 I4]].
  substs. apply binds_push_eq.

  forwards I1 : IHsub I4.
  apply~ binds_concat_left.
Qed.

Lemma denv_sub_dwft : forall E F A,
    dwft E A ->
    denv_sub F E ->
    dwft F A.
Proof.
  introv wf sub. generalize dependent F. inductions wf; introv sub.
  constructor~. apply denv_sub_ok with E; auto.
  constructor~. apply denv_sub_ok with E; auto.
  constructor~. apply denv_sub_ok with E; auto.
    apply* denv_sub_binds_tvar.
  constructor~. 
  apply_fresh dwft_all as x.
  apply~ H0.
Qed.

Lemma denv_sub_notin : forall E F x,
    x \notin dom E ->
    denv_sub F E ->
    x \notin dom F.
Proof.
  introv notin sub. inductions sub; auto.
Qed.

Lemma denv_sub_dmatch : forall E F A A1 A2,
    dmatch E A A1 A2 ->
    denv_sub F E ->
    dmatch F A A1 A2.
Proof.
  introv mat sub. generalize dependent F. inductions mat; introv sub.
  forwards ~ : IHmat sub.
  apply dmatch_all with tau; auto.
  apply denv_sub_dwft with E; auto.
  constructor~.
  constructor~.
Qed.

Lemma denv_sub_consub : forall E F A B,
    dconsub E A B ->
    denv_sub F E ->
    dconsub F A B.
Proof.
  introv csub sub. generalize dependent F. inductions csub; introv sub.
  constructor~. apply denv_sub_dokt with E; auto.
  constructor~. apply denv_sub_dokt with E; auto.
    apply* denv_sub_binds_tvar.
  constructor~. apply denv_sub_dokt with E; auto.
    apply* denv_sub_dwft.
  constructor~. apply denv_sub_dokt with E; auto.
    apply* denv_sub_dwft.
  constructor~. 
  apply dconsub_allL with tau; auto.
    apply* denv_sub_dwft.
  apply_fresh dconsub_allR as x; auto.
Qed.

Lemma dtyping'_strengthen : forall E F e A,
    dtyping' E e A ->
    denv_sub F E ->
    exists B, dtyping' F e B /\ dsub F B A.
Proof.
  introv ty sub. generalize dependent F.
  inductions ty; introv sub.

  -
  forwards ~ (B & [I1 I2]): denv_sub_binds_typ sub H0.
  exists B; auto.

  -
  exists dtyp_nat. splits~.
  constructor~. apply* denv_sub_dokt.
  constructor~. apply* denv_sub_dokt.

  -
  assert (I1 : dokt (E & x ~: A)). auto.
  assert (I2 : dokt E). apply* dokt_push_inv.
  assert (I3: dokt F). apply denv_sub_dokt with E; auto.
  forwards ~ [I4 [I5 I6]] : IHty (F & x ~: A).
    constructor~.
    apply~ dsub_refl.
    apply denv_sub_dwft with E; auto. apply* dokt_push_typ_inv.
    apply denv_sub_notin with E; auto. 
  exists (dtyp_arrow A I4). splits~.
  apply dtyping'_absann with x; auto.
  assert (x \notin dom F). apply denv_sub_notin with E; auto. auto.
  constructor~.
    apply~ dsub_refl.
    apply denv_sub_dwft with E; auto. apply* dokt_push_typ_inv.
  apply* dsub_strengthen_typ_push.

  -
  forwards (B1 & [I1 I2]) : IHty1 sub.
  forwards (B2 & [I3 I4]) : IHty2 sub.
  lets I5 : denv_sub_dmatch H sub.
  lets (C1 & C2 & [I6 [I7 I8]]): dmatch_sub I5 I2.
  exists C2. splits~.
  apply dtyping'_app with B1 C1 B2; auto.
  forwards ~ N1 : denv_sub_consub H0 sub.
  forwards ~ N2: dconsub_dsub_r N1 I7.
  forwards ~ N3: dconsub_dsub_l N2 I4.

  -
  assert (I1 : dokt (E & x ~: A)). auto.
  assert (I2 : dokt E). apply* dokt_push_inv.
  assert (I3: dokt F). apply denv_sub_dokt with E; auto.
  forwards (B1 & [I4 I5]) : IHty (F & x ~: A).
    constructor~.
    apply~ dsub_refl.
    apply denv_sub_dwft with E; auto. apply* dokt_push_typ_inv.
    apply denv_sub_notin with E; auto. 
  exists (dtyp_arrow A B1). splits~.
  apply dtyping'_abs with x; auto.
  assert (x \notin dom F). apply denv_sub_notin with E; auto. auto.
  constructor~.
    apply~ dsub_refl.
    apply denv_sub_dwft with E; auto. apply* dokt_push_typ_inv.
  apply* dsub_strengthen_typ_push.

  -
  forwards (B1 & [I1 I2]): IHty (F & a ~tvar).
  constructor~.
  apply denv_sub_notin with E; auto. 
  exists (dtyp_all (dclose_tt a B1)).
  splits~.
  apply dtyping'_gen with a.
  apply notin_union.
  split. apply denv_sub_notin with E; auto.
    apply~ dclose_tt_fresh.
  rewrite~ <- dclose_tt_open_var.
  lets [? [? ?]] : dtyping'_regular I1.
  auto.
  apply dsub'_dsub.
  apply dsub'_allR with a; auto.
  apply notin_union. split. apply denv_sub_notin with E; auto.
  apply notin_union. split~. simpl. apply~ dclose_tt_fresh.
  apply dsub'_allL with (dtyp_fvar a); auto.
  rewrite~ <- dclose_tt_open_var.
  apply~ dsub_dsub'.
  lets [? [? ?]] : dtyping'_regular I1. auto.

  -
  forwards ~ (B1 & [I1 I2]) : IHty1 sub.
  forwards ~ (B2 & [I3 I4]) : IHty2 (F & x ~: B1).
  constructor~.
  apply denv_sub_notin with E; auto.
  exists B2.  splits~.
  apply dtyping'_let with x B1; auto.
  apply notin_union. split~. apply denv_sub_notin with E; auto.
  apply* dsub_strengthen_typ_push.
Qed.

Lemma dtyping_bind_strengthen : forall E1 x A e B T1,
    dtyping (E1 & x ~: A) e T1 ->
    dsub (E1 & x ~: A) B A ->
    exists T2,
      dtyping (E1 & x ~: B) e T2
      /\ dsub (E1 & x ~: B) T2 T1.
Proof.
  introv ty su.
  assert (I1: dokt (E1 & x ~: A)).
    lets~ [? [? ?]] : dtyping_regular ty.
  assert (I2: dokt E1).
    apply* dokt_push_inv.
  assert (I3 : denv_sub (E1 & x ~: B) (E1 & x ~: A)).

    constructor~.
    apply* dsub_strengthen_typ_push.
    apply* dokt_push_inv.
    apply* dokt_push_inv.
  apply dtyping_dtyping' in ty.
  forwards (T & [I4 I5]): dtyping'_strengthen ty I3.
  exists T. splits~.
  apply~ dtyping'_dtyping.
Qed.    
