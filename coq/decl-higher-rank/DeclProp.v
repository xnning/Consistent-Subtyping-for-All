Set Implicit Arguments.
Require Import LibLN DeclDef.
Require Import DeclInfra.
Require Import DeclSub.

(** * SUBTYPING *)

Hint Constructors dsub dconsist.
Lemma dsub_refl: forall E t,
    dokt E ->
    dwft E t ->
    dsub E t t.
Proof.
  introv ok wf.
  induction wf; simpls~.
  apply_fresh dsub_allR as x.
  apply dsub_allL with (dtyp_fvar x); auto.
Qed.
Hint Resolve dsub_refl.

Hint Constructors dconsub.
Lemma dsub_consub: forall E A B,
    dsub E A B ->
    dconsub E A B.
Proof.
  introv sub. inductions sub; auto.
  apply dconsub_allL with tau; auto.
  apply_fresh dconsub_allR as x; auto.
Qed.
Hint Resolve dsub_consub.

Lemma dsub_weakening : forall F E x v A B,
    dsub (E & F) A B ->
    dokt (E & x ~ v & F) ->
    dsub (E & x ~ v & F) A B.
Proof.
  introv sub. gen v.
  inductions sub; introv okt; simpls~.

  apply dsub_allL with tau; auto.

  apply_fresh dsub_allR as x; auto.
  rewrite <- concat_assoc.
  apply~ H0.
  rewrite~ concat_assoc.
  rewrite~ concat_assoc.
Qed.

Lemma dsub_push : forall E x v A B,
    dsub E A B ->
    dokt (E & x ~ v) ->
    dsub (E & x ~ v) A B.
Proof.
  intros.
  apply_empty~ dsub_weakening.
Qed.

Lemma dwft_subst: forall A B E x,
    dwft E A ->
    dwft E B ->
    dwft E (dsubst_tt x A B).
Proof.
  introv wfa wfb.
  inductions wfb; simpls~.
  case_var~.
  apply_fresh dwft_all as x.
  forwards ~ : H0 y.
  apply~ dwft_push.
  rewrite~ dsubst_tt_open_tt_var.
Qed.

Lemma dsub_subst_var : forall A B z U E,
    dsub E A B ->
    dwft E U ->
    dtyp_mono U ->
    dsub E (dsubst_tt z U A) (dsubst_tt z U B).
Proof.
  introv Typt Typu mo. inductions Typt; introv; simpl; autos~.
  case_var*.

  rewrite dsubst_tt_open_tt in IHTypt; auto.
  apply dsub_allL with (dsubst_tt z U tau); auto.
  apply* dsubst_mono.
  apply~ dwft_subst.

  apply_fresh* dsub_allR as x.
  specializes H0 x.
  forwards * : H0.
  apply~ dwft_push.
  rewrite* dsubst_tt_open_tt_var.
Qed.

Lemma dsub_strengthen : forall F A B U E x v,
    dsub (E & x ~ v & F) A B ->
    dokt (E & F) ->
    dwft (E & F) U ->
    dtyp_mono U ->
    x \notin dfv_tt U ->
    dsub (E & F) (dsubst_tt x U A) (dsubst_tt x U B).
Proof.
  introv sub okt wft mono nin.
  inductions sub; introv; simpls~.
  case_var~.
  apply binds_remove in H0; auto.

  constructor~.
  apply~ IHsub1.
  apply~ IHsub2.

  apply dsub_allL with (dsubst_tt x U tau); auto.
  apply~ dsubst_mono.
  apply dwft_strengthen with x v; auto.
  apply~ dwft_subst.
  apply~ notin_subst.
  rewrite~ <- dsubst_tt_open_tt.
  apply~ IHsub.

  apply_fresh dsub_allR as x; auto.
  forwards ~ : H0 y (F & y ~tvar) E x v.
  rewrite ~ concat_assoc.
  rewrite ~ concat_assoc.
  rewrite ~ concat_assoc.
  apply~ dwft_push.
  rewrite concat_assoc in H1; auto.
  rewrite dsubst_tt_open_tt in H1; auto.
  simpls~. case_var~.
Qed.

Lemma dsub_remove_push : forall A B U E x v,
    dsub (E & x ~ v) A B ->
    dwft E U ->
    dtyp_mono U ->
    x \notin dfv_tt U ->
    dsub E (dsubst_tt x U A) (dsubst_tt x U B).
Proof.
  intros.
  apply_empty* dsub_strengthen.
  forwards ~ [? [? ?]] : dsub_regular H.
  apply~ dokt_concat_left_inv.
Qed.

Lemma dsub_strengthen_typ : forall F E x v A1 A2,
    dsub (E & x ~: v & F) A1 A2 ->
    dsub (E & F) A1 A2.
Proof.
  introv wf1.
  assert (dokt (E & F)).
  lets~ [? _] : dsub_regular wf1.
  apply* dokt_strengthen_typ.
  inductions wf1; try(constructor~); simpls~.

  tests : (x = x0).
  apply binds_middle_eq_inv in H0; auto.
  inversions H0.
  apply binds_remove in H0; auto.

  apply* IHwf1_1.
  apply* IHwf1_2.

  apply dsub_allL with tau; auto.
  apply* dwft_strengthen_typ.
  apply~ IHwf1.

  apply_fresh dsub_allR as x; auto.
  rewrite <- concat_assoc.
  apply H0 with (x1:=x) (v0:=v) (F0:= (F & y ~tvar)); auto.
  rewrite~ concat_assoc.
  rewrite~ concat_assoc.
Qed.

Lemma dsub_trans_help : forall m n E A B C n1 n2,
    num_of_all B < m ->
    n1 + n2 < n ->
    dsub_size E B C n1 ->
    dsub_size E A B n2 ->
    dsub E A C.
Proof.
  intro m. induction m; introv lem.
  inversion lem.

  gen A B C n1 n2 E.
  induction n; introv lem len sub21 sub32.
  inversion len.

  inductions sub21; subst~.

  (* nat *)
  inductions sub32; subst~.
  apply dsub_allL with tau; auto.
  apply* dsub_size_dsub.

  (* var *)
  inductions sub32; subst~.
  apply dsub_allL with tau; auto.
  apply* dsub_size_dsub.

  (* unknown *)
  apply* dsub_size_dsub.

  (* arrow *)
  clear IHsub21_1 IHsub21_2.
  inductions sub32; intros; subst~.
      (* arrow x arrow *)
      simpls. apply~ dsub_fun.
      forwards ~ : IHn sub32_1 sub21_1. Omega.omega. Omega.omega.
      forwards ~ : IHn sub21_2 sub32_2. Omega.omega. Omega.omega.
      (* all x arrow *)
      apply dsub_allL with tau; auto.
      forwards ~ : IHsub32 sub21_1 sub21_2.
      Omega.omega.

  (* alll *)
  clear IHsub21.
  inductions sub32; intros; subst~.
      (* alll x alll *)
      apply dsub_allL with tau0; auto.
      forwards ~ : IHsub32 IHn.
      Omega.omega.
      (* allr x alll *)
      clear H2.
      pick_fresh y. forwards ~ : H1 y. clear H1.
      lets: dsub_size_dsub H2.
      forwards ~ : dsub_remove_push tau y H1.
      rewrite dsubst_tt_fresh in H3; auto.
      rewrite dsubst_tt_open_tt in H3; auto. simpls~. case_var~.
      rewrite dsubst_tt_fresh in H3; auto.
      lets (ni1 & I1) : dsub_dsub_size H3.
      forwards ~ : IHm sub21 I1.
      rewrite~ num_of_all_open_mono. Omega.omega.

  (* allr *)
  apply_fresh dsub_allR as x; auto.
  apply~ H0. Omega.omega.
  apply~ dsub_size_push.
  constructor~.
  forwards ~ [? [? ?]] : dsub_size_regular sub32.
Qed.

Lemma dsub_trans : forall E A B C,
    dsub E A B ->
    dsub E B C ->
    dsub E A C.
Proof.
  introv sub21 sub32.
  lets (n1 & I1): dsub_dsub_size sub21.
  lets (n2 & I2): dsub_dsub_size sub32.
  apply* dsub_trans_help.
Qed.

Lemma dsub_match_arrow: forall E B A1 A2,
    dsub E B (dtyp_arrow A1 A2) ->
    exists B1 B2,
      dmatch E B B1 B2 /\
      dsub E  (dtyp_arrow B1 B2) (dtyp_arrow A1 A2).
Proof.
  introv sub. inductions sub; simpls~.
  exists ~ A0 A3. splits~. constructor~.
  destruct IHsub as (C1 & C2 & [? ?]).
  exists~ C1 C2. splits~.
  apply dmatch_all with tau; auto.
Qed.

(** * MATCH *)

Lemma dmatch_strengthen_typ : forall F E x A v A1 A2,
    dmatch (E & x ~: v & F) A A1 A2 ->
    dmatch (E & F) A A1 A2.
Proof.
  introv wf1.
  inductions wf1; try(constructor~); simpls~.

  apply dmatch_all with tau; auto.
  apply* dwft_strengthen_typ.
  apply~ IHwf1.
Qed.

Lemma dmatch_weakening : forall F E x A v A1 A2,
    dmatch (E & F) A A1 A2 ->
    ok (E & x ~ v & F) ->
    dmatch (E & x ~ v & F) A A1 A2.
Proof.
  introv wf1 okt.
  inductions wf1; try(constructor~); simpls~.

  apply dmatch_all with tau; auto.
Qed.

(** * CONSISTENCY *)

Lemma dconsist_symm : forall A B,
    dconsist A B ->
    dconsist B A.
Proof.
  introv cons. inductions cons; auto.
Qed.
Hint Resolve dconsist_symm.

Lemma dconsist_close : forall A B y,
    dconsist A B ->
    dconsist (dclose_tt y A) (dclose_tt y B).
Proof.
  introv con. unfold dclose_tt. generalize 0.
  inductions con; introv; simpls~.
Qed.

Lemma dconsist_open : forall A B tau,
    dconsist A B ->
    dconsist (dopen_tt A tau) (dopen_tt B tau).
Proof.
  introv con. unfold dopen_tt. generalize 0.
  inductions con; introv; simpls~.
Qed.

(** * UNKNOWN LIKE *)

Inductive dtyp_unknown_like : dtyp -> Prop :=
  | dtyp_unknown_like_intro:
      dtyp_unknown_like dtyp_unknown
  | dtyp_unknown_like_all: forall x,
      dtyp_unknown_like x ->
      dtyp_unknown_like (dtyp_all x)
.

Hint Constructors dtyp_unknown_like.

Lemma dmono_unknown_false : forall tau,
    dtyp_mono tau ->
    dtyp_unknown_like tau ->
    False.
Proof.
  introv mono unn. inductions mono; simpls~;
     try(solve[inversions~ unn]).
Qed.

Lemma dopen_unknown_like : forall A tau,
    dtyp_mono tau ->
    dtyp_unknown_like (dopen_tt A tau) ->
    dtyp_unknown_like A.
Proof.
  introv mono.
  unfolds dopen_tt.
  generalize 0.
  inductions A; introv unn; simpls~.
  inversions unn.
  case_nat~.
  forwards ~ : dmono_unknown_false mono unn. false~.
  inversions unn.
  constructor~. apply IHA with tau (S n); auto.
Qed.

Lemma dsub_unknown_r : forall E A,
    dsub E A dtyp_unknown ->
    dtyp_unknown_like A.
Proof.
  introv sub. inductions sub; simpls~.
  forwards~ : dopen_unknown_like H IHsub.
Qed.

Lemma dopen_unknown_like_fresh : forall A B,
    dtyp_unknown_like A ->
    dopen_tt A B = A.
Proof.
  introv unn.
  unfolds dopen_tt.
  generalize 0.
  inductions unn; introv; simpls~.
  f_equal~.
Qed.

Lemma dtyp_unknown_like_dsub_l: forall E A,
    dokt E ->
    dtyp_unknown_like A ->
    dsub E A dtyp_unknown.
Proof.
  introv okt un. inductions un.
  constructor~.
  apply dsub_allL with dtyp_nat; auto.
  rewrite~ dopen_unknown_like_fresh.
Qed.

Lemma dtyp_unknown_like_dsub_r: forall E A,
    dokt E ->
    dtyp_unknown_like A ->
    dsub E dtyp_unknown A.
Proof.
  introv okt un. inductions un.
  constructor~.
  apply_fresh dsub_allR as x. 
  rewrite~ dopen_unknown_like_fresh.
  apply_empty dsub_weakening; auto.
Qed.

Lemma dwft_unknown_like : forall E A,
    ok E ->
    dtyp_unknown_like A ->
    dwft E A.
Proof.
  introv okt unn. inductions unn; simpls~.
  apply_fresh dwft_all as x.
  rewrite~ dopen_unknown_like_fresh.
  apply~ dwft_push.
Qed.
Hint Resolve dwft_unknown_like.

Lemma dconsub_unknown_like_l : forall E A B,
    dokt E ->
    dtyp_unknown_like A ->
    dwft E B ->
    dconsub E A B.
Proof.
  introv okt unn wft.
  inductions unn; simpls~.
  apply dconsub_allL with dtyp_nat; auto.
  rewrite~ dopen_unknown_like_fresh.
Qed.

Lemma dconsub_unknown_like_r : forall E A B,
    dokt E ->
    dtyp_unknown_like A ->
    dwft E B ->
    dconsub E B A.
Proof.
  introv okt unn wft. gen E B.
  inductions unn; introv okt wft; simpls~.
  apply_fresh dconsub_allR as x; auto.
  rewrite~ dopen_unknown_like_fresh.
  apply~ IHunn.
  apply~ dwft_push.
Qed.

Lemma dmatch_arrow: forall E A A1 A2,
    dokt E ->
    dwft E A ->
    dmatch E A A1 A2 ->
    dsub E A (dtyp_arrow A1 A2) \/
    (dtyp_unknown_like A /\ A1 = dtyp_unknown /\ dtyp_unknown_like A2).
Proof.
  introv oke wft mat. inductions mat.
  forwards : IHmat; auto.
  apply~ dwft_open.
  destruct H1 as [sub | unn].
    left. apply dsub_trans with (dopen_tt A tau); auto.
      apply dsub_allL with tau; auto.
    right. destruct unn as [? [? ?]].
      splits~. constructor.
      eapply dopen_unknown_like.
      exact H. auto.
  left. apply~ dsub_refl.
  right. splits~. 
Qed.

Lemma unknonw_like_match: forall E A,
    ok E ->
    dtyp_unknown_like A ->
    exists B,
      dmatch E A dtyp_unknown B /\
      dtyp_unknown_like B.
Proof.
  introv oke un. inductions un.
  exists dtyp_unknown. splits~. constructor~.
  destruct IHun as (B & [? ?]).
  exists B; splits~.
  apply dmatch_all with dtyp_nat; auto.
  rewrite~ dopen_unknown_like_fresh.
Qed.


(** * CONSIST SUBTYPING *)


Lemma dconsub_refl: forall E t,
    dokt E ->
    dwft E t ->
    dconsub E t t.
Proof.
  introv ok wf.
  induction wf; simpls~.
  apply_fresh dconsub_allR as x.
  apply dconsub_allL with (dtyp_fvar x); auto.
Qed.


Lemma dconsub_strengthen_typ : forall F E x v A1 A2,
    dconsub (E & x ~: v & F) A1 A2 ->
    dconsub (E & F) A1 A2.
Proof.
  introv wf1.
  assert (dokt (E & F)).
  lets~ [? _] : dconsub_regular wf1.
  apply* dokt_strengthen_typ.
  inductions wf1; try(constructor~); simpls~.

  tests : (x = x0).
  apply binds_middle_eq_inv in H0; auto.
  inversions H0.
  apply binds_remove in H0; auto.
  apply* dwft_strengthen_typ.
  apply* dwft_strengthen_typ.
  apply* IHwf1_1.
  apply* IHwf1_2.

  apply dconsub_allL with tau; auto.
  apply* dwft_strengthen_typ.
  apply~ IHwf1.

  apply_fresh dconsub_allR as x; auto.
  rewrite <- concat_assoc.
  apply H0 with (x1:=x) (v0:=v) (F0:= (F & y ~tvar)); auto.
  rewrite~ concat_assoc.
  rewrite~ concat_assoc.
Qed.

Lemma dconsub_weakening : forall F E x v A1 A2,
    dconsub (E & F) A1 A2 ->
    dokt (E & x ~ v & F) ->
    dconsub (E & x ~ v & F) A1 A2.
Proof.
  introv wf1 okt.
  inductions wf1; try(constructor~); simpls~.

  apply~ binds_weaken.

  apply dconsub_allL with tau; auto.

  apply_fresh dconsub_allR as x; auto.
  rewrite <- concat_assoc.
  apply~ H0.
  rewrite~ concat_assoc.
  rewrite~ concat_assoc.
Qed.


Lemma dconsub_through_subst_tt : forall E F A B a T,
  dconsub (E & a ~tvar & F) A B ->
  dwft E T ->
  dtyp_mono T ->
  dconsub (E & map (dsubst_tb a T) F) (dsubst_tt a T A) (dsubst_tt a T B).
Proof.
  introv SsubT WF Mono.
  inductions SsubT; introv; simpl dsubst_tt.

  (* int *)
  apply* dconsub_refl.
  (* var *)
  case_var.
  apply* dconsub_refl. apply_empty* dwft_weaken.
  apply* dconsub_refl.
  inversions H0. binds_cases H2.
  apply* dwft_var.
  assert (binds x dbind_tvar (map (dsubst_tb a T) F)).
  assert (dbind_tvar = dsubst_tb a T dbind_tvar). reflexivity.
  rewrite H0.
  apply* binds_map.
  apply* dwft_var.

  (* unknown *)
  apply* dconsub_unknown_l.
  apply* dconsub_unknown_r.
  (* Fun *)
  apply* dconsub_fun.
  (* ForallL *)
  apply dconsub_allL with (tau := dsubst_tt a T tau); autos.
  apply* dsubst_mono.
  rewrite* <- dsubst_tt_open_tt.
  (* ForallR *)
  apply_fresh dconsub_allR as x.
  rewrite* dsubst_tt_open_tt_var.
  assert (dbind_tvar = dsubst_tb a T dbind_tvar). reflexivity.
  rewrite H1.
  apply_ih_map_bind* H0.
Qed.

Lemma dconsub_mono_eq : forall A B E,
    dtyp_mono A ->
    dtyp_mono B ->
    dconsub E A B ->
    A = B.
Proof.
  introv Mono1 Mono2 Sub.
  induction* Sub; try inverts* Mono1; try inverts* Mono2.
  forwards * : IHSub1.
  forwards * : IHSub2.
  congruence.
Qed.


Hint Constructors dsub'.
Lemma dconsub_prop': forall E A B,
    dconsub E A B ->
    exists C D, dsub' E A C /\ dconsist C D /\ dsub' E D B
.
Proof.
  introv sub. inductions sub.
  exists ~ dtyp_nat dtyp_nat.
  exists ~ (dtyp_fvar x) (dtyp_fvar x).
  exists~ dtyp_unknown A.
  exists~ A dtyp_unknown.

  destruct IHsub1 as (C1 & D1 & [? [? ?]]).
  destruct IHsub2 as (C2 & D2 & [? [? ?]]).
  exists ~ (dtyp_arrow D1 C2) (dtyp_arrow C1 D2).

  destruct IHsub as (C1 & D1 & [? [? ?]]).
  exists ~ C1 D1. splits~. apply dsub'_allL with tau; auto.

  pick_fresh y.
  forwards ~ (C1 & D1 & [? [? ?]]) : H0 y.
  exists~ (dtyp_all (dclose_tt y C1)) (dtyp_all (dclose_tt y D1)). splits~.

  apply dsub'_allR with y; auto.
  assert (y \notin dfv_tt (dclose_tt y C1)). apply~ dclose_tt_fresh.
  auto.
  rewrite~ <- dclose_tt_open_var.
  forwards ~ [? [? ?]] : dsub'_regular H1.

  constructor~.
  apply~ dconsist_close.

  apply dsub'_allR with y; auto.
  assert (y \notin dfv_tt (dclose_tt y D1)). apply~ dclose_tt_fresh.
  auto.
  apply dsub'_allL with (dtyp_fvar y); auto.
  rewrite~ <- dclose_tt_open_var.
  forwards ~ [? [? ?]] : dsub'_regular H3.
Qed.

Lemma dconsub_prop1: forall E A B,
    dconsub E A B ->
    exists C D, dsub E A C /\ dconsist C D /\ dsub E D B
.
Proof.
  introv sub.
  forwards ~ (C1 & D1 & [? [? ?]]): dconsub_prop' sub.
  exists ~ C1 D1. splits~.
  apply* dsub'_dsub.
  apply* dsub'_dsub.
Qed.

Lemma dconsub_prop'2: forall m n E A B C D n1 n2,
    num_of_all C + num_of_all D < m ->
    n1 + n2 < n ->
    dsub_size E A C n1 ->
    dconsist C D ->
    dsub_size E D B n2 ->
    dconsub E A B
.
Proof.
  intro m. induction m; introv lem.
  inversion lem.

  gen A B C D n1 n2.
  inductions n; introv lem len sub1 cons sub2.
  inversions len.

  inductions sub2.

  (* nat *)
  apply dsub_size_dsub in sub1.
  inversions cons; auto.
  forwards ~ : dsub_unknown_r sub1.
  apply* dconsub_unknown_like_l.

  (* fvar *)
  apply dsub_size_dsub in sub1.
  inversions cons; auto.
  forwards ~ : dsub_unknown_r sub1.
  apply* dconsub_unknown_like_l.

  (* unknown *)
  apply dsub_size_dsub in sub1.
  apply~ dconsub_unknown_like_r.

  (* arrow *)
  forwards ~ I1 : dsub_size_dsub sub1.
  forwards ~ I2 : dsub_size_dsub sub2_1.
  forwards ~ I3 : dsub_size_dsub sub2_2.

  inversions cons; auto.
  assert (dsub E (dtyp_arrow A1 A2) (dtyp_arrow B1 B2)) by autos~.
  forwards ~ : dsub_trans I1 H.

  forwards ~ : dsub_unknown_r I1.
  apply* dconsub_unknown_like_l.

  inversions sub1. simpls.
  forwards ~ : dconsist_symm H2.
  forwards ~ : IHn sub2_1 H H5. Omega.omega. Omega.omega.
  forwards ~ : IHn H7 H3 sub2_2. Omega.omega. Omega.omega.

  apply dconsub_allL with tau; auto.
  assert (N1 : dconsist (dtyp_arrow A0 A3) (dtyp_arrow A1 A2)) by autos~.
  assert (N2 : dsub_size E (dtyp_arrow A1 A2) (dtyp_arrow B1 B2) (1 + n0 + n2)) by autos~.
  forwards ~ : IHn H1 N1 N2. Omega.omega.

  (* allL *)
  forwards ~ I1 : dsub_size_dsub sub1.
  forwards ~ I2 : dsub_size_dsub sub2.

  inversions cons.
  assert (dsub E (dtyp_all A2) (dopen_tt A2 tau)).
    apply dsub_allL with tau; auto.
  forwards ~ : dsub_trans I1 H1.
  forwards ~ : dsub_trans H2 I2.

  forwards ~ : dsub_unknown_r I1.
  apply* dconsub_unknown_like_l.

  inversions sub1.
  apply dconsub_allL with tau0; auto.
  assert (N1 : dconsist (dtyp_all A0) (dtyp_all A2)) by autos~.
  assert (N2 : dsub_size E (dtyp_all A2) B2 (1 + n0)).
    apply dsub_size_allL with tau; auto.
  forwards ~ : IHn H4 N1 N2. Omega.omega.

  clear IHsub2.
  assert (N1: dsub E A (dtyp_all A0)).
  apply_fresh dsub_allR as x.
  forwards ~ : H5 x.
  apply* dsub_size_dsub.
  assert (N2 : dsub E (dtyp_all A0) (dopen_tt A0 tau)).
  apply dsub_allL with tau; auto.
  apply~ dsub_refl.
  apply~ dwft_open.
  forwards ~ N3: dsub_trans N1 N2.
  assert (N4 : dconsist (dopen_tt A0 tau) (dopen_tt A2 tau)).
    apply~ dconsist_open.
  forwards ~ (nn & N5) : dsub_dsub_size N3.
  forwards ~ : IHm N5 N4 sub2.
  rewrite~ num_of_all_open_mono.
  rewrite~ num_of_all_open_mono.
  simpls. Omega.omega.

  (* allR *)
  apply_fresh dconsub_allR as x.
  forwards ~ : (H x).
  forwards ~ : dsub_size_push x dbind_tvar sub1.
  constructor~.
  forwards ~ [? [? ?]] : dsub_size_regular sub1.
  forwards ~ : IHn H2 cons H1. Omega.omega.
Qed.

Lemma dconsub_prop2: forall E A B C D,
    dsub E A C ->
    dconsist C D ->
    dsub E D B ->
    dconsub E A B
.
Proof.
  introv sub1 con sub2.
  lets (n1 & subs1) : dsub_dsub_size sub1.
  lets (n2 & subs2) : dsub_dsub_size sub2.
  apply dconsub_prop'2 with (n1:= n1) (n2:=n2) (C:= C) (D:=D) (m := S (num_of_all C + num_of_all D)) (n := S (n1 + n2)); auto.
Qed.

Lemma dconsub_dsub: forall E A B C,
    dconsub E A B ->
    dsub E B C ->
    dconsub E A C.
Proof.
  introv csub sub.
  apply dconsub_prop1 in csub.
  destruct csub as (D1 & D2 & [? [? ?]]).
  apply dconsub_prop2 with D1 D2; auto.
  apply dsub_trans with B; auto.
Qed.

(** * STATIC *)

Inductive dtyp_static : dtyp -> Prop :=
  | dtyp_static_nat:
      dtyp_static dtyp_nat
  | dtyp_static_fvar: forall i,
      dtyp_static (dtyp_fvar i)
  | dtyp_static_arrow: forall A B,
      dtyp_static A ->
      dtyp_static B ->
      dtyp_static (dtyp_arrow A B)
  | dtyp_static_all: forall L A,
      (forall x, x \notin L -> dtyp_static (A dopen_tt_var x)) ->
      dtyp_static (dtyp_all A)
.

Inductive dterm_static : dtrm -> Prop :=
  | dterm_static_var: forall x,
      dterm_static (dtrm_fvar x)
  | dterm_static_nat : forall i,
      dterm_static (dtrm_nat i)
  | dterm_static_absann : forall L V e1,
      dtyp_static V ->
      (forall x, x \notin L -> dterm_static (e1 dopen_ee_var x)) ->
      dterm_static (dtrm_absann V e1)
  | dterm_static_abs : forall L e1,
      (forall x, x \notin L -> dterm_static (e1 dopen_ee_var x)) ->
      dterm_static (dtrm_abs e1)
  | dterm_static_app : forall e1 e2,
      dterm_static e1 ->
      dterm_static e2 ->
      dterm_static (dtrm_app e1 e2)
.

Inductive denv_static : denv -> Prop :=
  | denv_static_empty : denv_static empty
  | denv_static_typ : forall E x T,
      denv_static E ->
      dtyp_static T ->
      dwft E T ->
      x # E ->
      denv_static (E & x ~: T)
  | denv_static_tvar : forall E x,
      denv_static E ->
      x # E ->
      denv_static (E & x ~tvar)
.

(** Properties for static *)

Hint Constructors denv_static dterm_static dtyp_static.

Hint Constructors dtype dterm.

Lemma dtyp_static_dtype : forall A,
    dtyp_static A ->
    dtype A.
Proof.
  introv ty. inductions ty; simpls~.
  apply_fresh dtype_all as x.
  apply~ H0.
Qed.

Lemma dterm_static_dterm: forall e,
    dterm_static e ->
    dterm e.
Proof.
  introv dm. inductions dm; auto.
  apply_fresh dterm_absann as x.
  apply* dtyp_static_dtype.
  apply~ H1.
  apply_fresh dterm_abs as x.
  apply~ H0.
Qed.

Lemma denv_static_dokt: forall e,
    denv_static e ->
    dokt e.
Proof.
  introv dm. inductions dm; auto.
Qed.

Lemma denv_static_dtyp: forall e x T,
    denv_static e ->
    binds x (dbind_typ T) e ->
    dtyp_static T.
Proof.
  introv dm bd. inductions dm.
  false* binds_empty_inv.
  forwards [[? ?] | [? ?]] : binds_push_inv bd.
  inversions H3. subst~.
  apply~ IHdm.
  forwards [[? ?] | [? ?]] : binds_push_inv bd.
  inversions H1.
  apply~ IHdm.
Qed.

Lemma denv_static_push_inv: forall e x T,
    denv_static (e & x ~ T) ->
    denv_static e.
Proof.
  introv dm. inductions dm; auto.
  false* empty_push_inv.
  forwards [? [? ?]]:  eq_push_inv x.
  subst~.
  forwards [? [? ?]]:  eq_push_inv x.
  subst~.
Qed.

Lemma denv_static_push_inv_dtyp: forall e x T,
    denv_static (e & x ~: T) ->
    dtyp_static T.
Proof.
  introv dm. inductions dm; auto.
  false* empty_push_inv.
  forwards [? [? ?]]:  eq_push_inv x.
  inversions H3. subst~.
  forwards [? [? ?]]:  eq_push_inv x.
  inversions H1.
Qed.

Lemma denv_static_concat_inv: forall e f,
    denv_static (e & f) ->
    denv_static e.
Proof.
  introv dm. induction f using env_ind.
  rewrite concat_empty_r in dm; auto.
  rewrite concat_assoc in dm.
  lets: denv_static_push_inv dm.
  apply~ IHf.
Qed.

Lemma dtyp_static_consist: forall A B,
    dtyp_static A ->
    dtyp_static B ->
    dconsist A B ->
    A = B.
Proof.
  introv ta tb con.
  gen B. inductions ta; introv tb con; inversions~ con;
           try(solve[inversions tb]).
  inversions~ tb. f_equal~.

  inversions tb.
  pick_fresh y.
  forwards ~ : H3 y.
  forwards ~ : H0 y H1.
  apply~ dconsist_open.
  f_equal~.
  apply* dopen_tt_rec_inj.
Qed.

Lemma dtyp_mono_static : forall A,
    dtyp_mono A ->
    dtyp_static A.
Proof.
  introv mono. inductions mono; simpls~.
Qed.

Lemma dtyp_static_open' : forall m A B C,
    num_of_all A < m ->
    dtype B -> dtype C ->
    dtyp_static (dopen_tt A B) ->
    dtyp_static C ->
    dtyp_static (dopen_tt A C).
Proof.
  unfolds dopen_tt. generalize 0.

  intros n m. gen n. inductions m; introv lem.
  inversions lem.

  introv tyb tyc da. gen C.
  inductions da; introv tyc db; simpls~.

  destruct A; simpls~; try(solve[inversions~ x]).
  case_nat~.

  destruct A; simpls~; try(solve[inversions~ x]).
  case_nat~.

  destruct A; simpls~; try(solve[inversions~ x]).
  inversions x.
  constructor~. apply IHda1 with B; auto. Omega.omega.
  apply IHda2 with B; auto. Omega.omega.
  case_nat~.

  destruct A; simpls~; try(solve[inversions~ x]).
  case_nat~.
  inversions x.
  apply_fresh dtyp_static_all as x; auto.
  unfolds dopen_tt.
  rewrite~ dopen_tt_rec_type_commu.
  apply IHm with B; auto.
  rewrite~ num_of_all_open_rec_mono.
  Omega.omega.
  rewrite~ dopen_tt_rec_type_commu.
Qed.

Lemma dtyp_static_open : forall A B C,
    dtype B -> dtype C ->
    dtyp_static (dopen_tt A B) ->
    dtyp_static C ->
    dtyp_static (dopen_tt A C).
Proof.
  intros.
  apply dtyp_static_open' with (1 + num_of_all A) B; auto.
Qed.

Lemma dmatch_static_preserve : forall E A A1 A2,
    dmatch E A A1 A2 ->
    dtyp_static A ->
    dtyp_static A1 /\ dtyp_static A2.
Proof.
  introv mat st. inductions mat; simpls~.
  apply~ IHmat.
  inversions~ st.
  pick_fresh y.
  apply dtyp_static_open with (dtyp_fvar y); auto.
  apply~ dtyp_mono_static.
  inversions~ st.
Qed.

Lemma dtyping_static_preserve : forall E e T,
    dtyping E e T ->
    denv_static E ->
    dterm_static e ->
    dtyp_static T.
Proof.
  introv Hty Hen Htm.
  inductions Hty; auto.

  apply* denv_static_dtyp.

  inversions Htm.
  apply~ dtyp_static_arrow.
  pick_fresh y. apply H1 with y; auto. constructor~.
  forwards ~ : H0 y.
  lets [? [? ?]] : dtyping_regular H2.
  lets~ : dokt_push_typ_inv H3.

  inversions Htm.
  forwards ~ : IHHty1.
  inversions H;
  inversions~ H1.
  forwards ~ [? ?] : dmatch_static_preserve H6 .
  pick_fresh y.
  apply dtyp_static_open with (dtyp_fvar y); auto.
  apply~ dtyp_mono_static.

  inversions Htm.
  apply~ dtyp_static_arrow.
  apply~ dtyp_mono_static.
  pick_fresh y. apply H1 with y; auto. constructor~.
  apply~ dtyp_mono_static.
  forwards ~ : H0 y.
  lets [? [? ?]] : dtyping_regular H2.
  lets~ : dokt_push_typ_inv H4.

  apply_fresh dtyp_static_all as x.
  apply~ H0.
Qed.

Lemma dsub_static: forall E A B,
    dsub E A B ->
    (dtyp_static A <->
     dtyp_static B).
Proof.
  introv sub.
  inductions sub;
  splits~; introv sta; f_equal~.
  inversions sta. constructor~. apply~ IHsub1. apply~ IHsub2.
  inversions sta. constructor~. apply~ IHsub1. apply~ IHsub2.
  apply~ IHsub.
  inversions sta.
  pick_fresh y. forwards ~ : H2 y.
  apply* dtyp_static_open.
  apply* dtyp_mono_static.

  apply_fresh dtyp_static_all as x; auto.
  apply IHsub in sta.
  apply dtyp_static_open with tau; auto.

  apply_fresh dtyp_static_all as x; auto.
  apply~ H0.

  inversions sta.
  pick_fresh y. forwards ~ : H0 y.
  apply~ H1.
Qed.

Lemma dsub_static_l: forall E A B,
    dsub E A B ->
    dtyp_static A ->
    dtyp_static B.
Proof.
  intros.
  forwards ~ : dsub_static H.
  apply~ H1.
Qed.

Lemma dsub_static_r: forall E A B,
    dsub E A B ->
    dtyp_static B ->
    dtyp_static A.
Proof.
  intros.
  forwards ~ : dsub_static H.
  apply~ H1.
Qed.

Lemma dconsub_static_sub: forall E A B,
    dconsub E A B ->
    dtyp_static A ->
    dtyp_static B ->
    dsub E A B.
Proof.
  introv sub ta tb.
  inductions sub; auto; try solve [inversions~ ta];
   try solve [inversions~ tb].
  inversions ta. inversions tb. constructor~.

  apply dsub_allL with tau; auto.
  apply~ IHsub.
  inversions ta. pick_fresh y. forwards~ : H2 y.
  apply dtyp_static_open with (dtyp_fvar y); auto.
  apply~ dtyp_mono_static.

  inversion~ tb.
  apply_fresh dsub_allR as x; auto.
Qed.

(** * LESS PRECISE *)

Inductive dtyp_less_precise : dtyp -> dtyp -> Prop :=
  | dtyp_less_precise_unknown: forall A,
      dtype A ->
      dtyp_less_precise dtyp_unknown A
  | dtyp_less_precise_tvar: forall x,
      dtyp_less_precise (dtyp_fvar x) (dtyp_fvar x)
  | dtyp_less_precise_nat:
      dtyp_less_precise dtyp_nat dtyp_nat
  | dtyp_less_precise_arrow: forall A1 A2 B1 B2,
      dtyp_less_precise A1 B1 ->
      dtyp_less_precise A2 B2 ->
      dtyp_less_precise (dtyp_arrow A1 A2) (dtyp_arrow B1 B2)
  | dtyp_less_precise_all: forall L A1 A2,
      (forall x, x \notin L ->
            dtyp_less_precise (A1 dopen_tt_var x) (A2 dopen_tt_var x)) ->
      dtyp_less_precise (dtyp_all A1) (dtyp_all A2)
.

Inductive dtyp_less_precise' : dtyp -> dtyp -> Prop :=
  | dtyp_less_precise'_unknown: forall A,
      dtype A ->
      dtyp_less_precise' dtyp_unknown A
  | dtyp_less_precise'_tvar: forall x,
      dtyp_less_precise' (dtyp_fvar x) (dtyp_fvar x)
  | dtyp_less_precise'_nat:
      dtyp_less_precise' dtyp_nat dtyp_nat
  | dtyp_less_precise'_arrow: forall A1 A2 B1 B2,
      dtyp_less_precise' A1 B1 ->
      dtyp_less_precise' A2 B2 ->
      dtyp_less_precise' (dtyp_arrow A1 A2) (dtyp_arrow B1 B2)
  | dtyp_less_precise'_all: forall x A1 A2,
      x \notin dfv_tt A1 \u dfv_tt A2 ->
      dtyp_less_precise' (A1 dopen_tt_var x) (A2 dopen_tt_var x) ->
      dtyp_less_precise' (dtyp_all A1) (dtyp_all A2)
.

Inductive dterm_less_precise : dtrm -> dtrm -> Prop :=
  | dterm_less_precise_fvar : forall x,
      dterm_less_precise (dtrm_fvar x) (dtrm_fvar x)
  | dterm_less_precise_nat : forall i,
      dterm_less_precise (dtrm_nat i) (dtrm_nat i)
  | dterm_less_precise_absann: forall L e1 e2 A1 A2,
      dtyp_less_precise A1 A2 ->
      (forall x, x \notin L ->
      dterm_less_precise (e1 dopen_ee_var x)
                         (e2 dopen_ee_var x)) ->
      dterm_less_precise (dtrm_absann A1 e1) (dtrm_absann A2 e2)
  | dterm_less_precise_app : forall e1 e2 e3 e4,
      dterm_less_precise e1 e2 ->
      dterm_less_precise e3 e4 ->
      dterm_less_precise (dtrm_app e1 e3) (dtrm_app e2 e4)
  | dterm_less_precise_abs: forall L e1 e2,
      (forall x, x \notin L ->
      dterm_less_precise (e1 dopen_ee_var x)
                         (e2 dopen_ee_var x)) ->
      dterm_less_precise (dtrm_abs e1) (dtrm_abs e2)
.

Inductive dterm_less_precise' : dtrm -> dtrm -> Prop :=
  | dterm_less_precise'_fvar : forall x,
      dterm_less_precise' (dtrm_fvar x) (dtrm_fvar x)
  | dterm_less_precise'_nat : forall i,
      dterm_less_precise' (dtrm_nat i) (dtrm_nat i)
  | dterm_less_precise'_absann: forall x e1 e2 A1 A2,
      dtyp_less_precise A1 A2 ->
      x  \notin (dfv_ee e1 \u dfv_ee e2) ->
      dterm_less_precise' (e1 dopen_ee_var x)
                         (e2 dopen_ee_var x) ->
      dterm_less_precise' (dtrm_absann A1 e1) (dtrm_absann A2 e2)
  | dterm_less_precise'_abs: forall x e1 e2,
      x  \notin (dfv_ee e1 \u dfv_ee e2) ->
      dterm_less_precise' (e1 dopen_ee_var x)
                         (e2 dopen_ee_var x) ->
      dterm_less_precise' (dtrm_abs e1) (dtrm_abs e2)
  | dterm_less_precise'_app : forall e1 e2 e3 e4,
      dterm_less_precise' e1 e2 ->
      dterm_less_precise' e3 e4 ->
      dterm_less_precise' (dtrm_app e1 e3) (dtrm_app e2 e4)
.

Inductive denv_less_precise : denv -> denv -> Prop :=
  | denv_less_precise_refl: forall E,
      dokt E ->
      denv_less_precise E E
  | denv_less_precise_typ: forall E F x A1 A2,
      denv_less_precise E F ->
      dtyp_less_precise A1 A2 ->
      x # E -> x # F ->
      dwft E A1 ->
      dwft F A2 ->
      denv_less_precise (E & x ~: A1) (F & x ~: A2)
  | denv_less_precise_tvar: forall E F x,
      denv_less_precise E F ->
      x # E -> x # F ->
      denv_less_precise (E & x ~tvar) (F & x ~tvar)
.

(** Properties for dterm less precise *)

Hint Constructors dtyp_less_precise dterm_less_precise dterm_less_precise'.
Hint Constructors dterm.

Lemma dtyp_less_precise_refl: forall A,
    dtype A ->
    dtyp_less_precise A A.
Proof.
  introv ty. inductions ty; simpls~.
  apply_fresh dtyp_less_precise_all as x; auto.
Qed.
Hint Resolve dtyp_less_precise_refl.

Lemma dterm_less_precise_refl: forall e1,
    dterm e1 ->
    dterm_less_precise e1 e1.
Proof.
  introv dm. inductions dm; simpls~.
  apply_fresh dterm_less_precise_absann as x; auto.
  apply_fresh dterm_less_precise_abs as x; auto.
Qed.

Lemma dtyp_less_precise_dtype: forall A1 A2,
    dtyp_less_precise A1 A2 ->
    dtype A1 /\ dtype A2.
Proof.
  introv ty. inductions ty; simpls~.
  destruct IHty1. destruct IHty2. splits~.
  splits~.
  apply_fresh dtype_all as x; auto.
  forwards ~ [? ?] : H0 x.
  apply_fresh dtype_all as x; auto.
  forwards ~ [? ?] : H0 x.
Qed.

Hint Resolve dtyp_less_precise_dtype.

Lemma dterm_less_precise_dterm: forall e1 e2,
    dterm_less_precise e1 e2 ->
    dterm e1 /\ dterm e2.
Proof.
  introv dm. inductions dm; auto.
  split.
  apply_fresh dterm_absann as x.
  forwards ~ [? ?] : dtyp_less_precise_dtype H.
  forwards ~ : H1 x.
  destruct ~ H2.

  apply_fresh dterm_absann as x.
  forwards ~ [? ?] : dtyp_less_precise_dtype H.
  forwards ~ : H1 x.
  destruct ~ H2.

  destruct IHdm1. destruct IHdm2.
  split~.

  split.
  apply_fresh dterm_abs as x.
  forwards ~ : H0 x.
  destruct ~ H1.

  apply_fresh dterm_abs as x.
  forwards ~ : H0 x.
  destruct ~ H1.
Qed.

Lemma dterm_less_precise_precise' : forall e1 e2,
    dterm_less_precise e1 e2 ->
    dterm_less_precise' e1 e2.
Proof.
  introv dm.
  inductions dm; auto.
  pick_fresh y.
  apply~ dterm_less_precise'_absann.
  pick_fresh y.
  apply~ dterm_less_precise'_abs.
Qed.

Lemma dterm_less_precise_subst : forall t s u z,
    dterm_less_precise t s ->
    dterm_less_precise (dsubst_ee z (dtrm_fvar u) t)
                       (dsubst_ee z (dtrm_fvar u) s)
.
Proof.
  introv dm. inductions dm; simpls.
  case_var~.
  apply~ dterm_less_precise_refl.

  apply_fresh dterm_less_precise_absann as x; auto.
  specializes H1 x. forwards ~ : H1.
  rewrite* dsubst_ee_open_ee_var.
  rewrite* dsubst_ee_open_ee_var.

  apply* dterm_less_precise_app.

  apply_fresh dterm_less_precise_abs as x; auto.
  specializes H0 x. forwards ~ : H0.
  rewrite* dsubst_ee_open_ee_var.
  rewrite* dsubst_ee_open_ee_var.
Qed.

Lemma dterm_less_precise_rename : forall x y t s,
  dterm_less_precise (s dopen_ee_var x) (t dopen_ee_var x) ->
  x \notin dfv_ee s \u dfv_ee t ->
  y \notin dfv_ee s \u dfv_ee t ->
  dterm_less_precise (s dopen_ee_var y) (t dopen_ee_var y)
.
Proof.
  introv dm hx hy.
  tests: (x = y). subst*.
  rewrite~ (@dsubst_ee_intro x).
  pattern (t dopen_ee_var y) at 1; rewrite~ (@dsubst_ee_intro x).
  apply~ dterm_less_precise_subst.
Qed.

Lemma dterm_less_precises'_precise : forall e1 e2,
    dterm_less_precise' e1 e2 ->
    dterm_less_precise e1 e2.
Proof.
  introv dm.
  inductions dm; auto.
  apply_fresh dterm_less_precise_absann as y; auto.
  apply* dterm_less_precise_rename.
  apply_fresh dterm_less_precise_abs as y; auto.
  apply* dterm_less_precise_rename.
Qed.

(** Properties for dtype less precise *)

Hint Resolve dtyp_less_precise_refl.

Lemma dtyp_less_precise_trans: forall A B C,
    dtyp_less_precise A B ->
    dtyp_less_precise B C ->
    dtyp_less_precise A C.
Proof.
  introv ab bc. gen A. inductions bc; introv ab; auto.
  inversions ab. constructor~.
  inversions ab. constructor~. constructor~.
    forwards ~ [? ?] : dtyp_less_precise_dtype bc1.
    forwards ~ [? ?] : dtyp_less_precise_dtype bc2.
  f_equal~.

  inversions ab; auto.
  constructor~.
  apply_fresh dtype_all as x.
  forwards ~ : H x.
  forwards ~ [? ?] : dtyp_less_precise_dtype H2.
  apply_fresh dtyp_less_precise_all as x; auto.
Qed.

Hint Constructors dtyp_less_precise dtyp_less_precise'.
Lemma dtyp_less_precise_precise' : forall A B,
    dtyp_less_precise A B ->
    dtyp_less_precise' A B.
Proof.
  introv dm.
  inductions dm; auto.
  pick_fresh y.
  apply dtyp_less_precise'_all with y; auto.
Qed.

Lemma dtyp_less_precise_subst : forall t s u z,
    dtyp_less_precise t s ->
    dtyp_less_precise (dsubst_tt z (dtyp_fvar u) t)
                      (dsubst_tt z (dtyp_fvar u) s)
.
Proof.
  introv dm. inductions dm; simpls~.
  case_var~.

  apply_fresh dtyp_less_precise_all as x; auto.
  specializes H0 x. forwards ~ : H0.
  rewrite* dsubst_tt_open_tt_var.
  rewrite* dsubst_tt_open_tt_var.
Qed.

Lemma dtyp_less_precise_rename : forall x y t s,
  dtyp_less_precise (s dopen_tt_var x) (t dopen_tt_var x) ->
  x \notin dfv_tt s \u dfv_tt t ->
  y \notin dfv_tt s \u dfv_tt t ->
  dtyp_less_precise (s dopen_tt_var y) (t dopen_tt_var y)
.
Proof.
  introv dm hx hy.
  tests: (x = y). subst*.
  rewrite~ (@dsubst_tt_intro x).
  pattern (t dopen_tt_var y) at 1; rewrite~ (@dsubst_tt_intro x).
  apply~ dtyp_less_precise_subst.
Qed.

Lemma dtyp_less_precise'_precise : forall e1 e2,
    dtyp_less_precise' e1 e2 ->
    dtyp_less_precise e1 e2.
Proof.
  introv dm.
  inductions dm; auto.
  apply_fresh dtyp_less_precise_all as y; auto.
  apply* dtyp_less_precise_rename.
Qed.

Lemma dtyp_less_precise'_refl : forall A,
    dtype A ->
    dtyp_less_precise' A A.
Proof.
  introv ty. inductions ty; simpls~.
  pick_fresh x.
  apply dtyp_less_precise'_all with x; auto.
Qed.
Hint Resolve dtyp_less_precise'_refl.

(** the input to dmatch becomes dtyp less precise *)

Lemma dtyp_less_precise_open': forall m A B y t,
    num_of_all A + num_of_all B < m ->
    y \notin dfv_tt A \u dfv_tt B ->
    dtyp_less_precise (A dopen_tt_var y)
                      (B dopen_tt_var y) ->
    dtype t ->
    dtyp_less_precise (dopen_tt A t)
                      (dopen_tt B t).
Proof.
  unfolds dopen_tt. generalize 0.
  intros n m. gen n. inductions m; introv lem.
  inversions lem.

  introv nin mat ty. inductions mat; simpls~.

  destruct A; simpls~; try(solve[inversions~ x]).
  constructor~.
  rewrite dsubst_tt_rec_intro with (X:=y); auto.
  case_nat~.

  destruct A; simpls~; try(solve[inversions~ x1]).
  case_nat~. inversions~ x1.
  destruct B; simpls~; try(solve[inversions~ x]).
  case_nat~. inversions~ x.
  false~ notin_same.
  inversions~ x1.
  destruct B; simpls~; try(solve[inversions~ x]).
  case_nat~. inversions~ x.
  false~ notin_same.

  destruct A; simpls~; try(solve[inversions~ x0]).
  destruct B; simpls~; try(solve[inversions~ x]).
  case_nat~.
  case_nat~.

  destruct A; simpls~; try(solve[inversions~ x0]).
  inversions~ x0.
  destruct B; simpls~; try(solve[inversions~ x]).
  inversions~ x.
  constructor~.
  apply~ IHmat1. Omega.omega.
  apply~ IHmat2. Omega.omega.
  case_nat~.
  case_nat~.

  destruct A; simpls~; try(solve[inversions~ x0]).
  case_nat~.
  destruct B; simpls~; try(solve[inversions~ x]).
  case_nat~.
  inversions~ x0. inversions~ x.
  apply_fresh dtyp_less_precise_all as x; auto.
  clear H0.
  unfolds dopen_tt.
  rewrite~ dopen_tt_rec_type_commu.
  pattern
    (dopen_tt_rec 0 (dtyp_fvar x) (dopen_tt_rec (S n) t B)) at 1;
  rewrite~ dopen_tt_rec_type_commu.
  apply IHm with (y:=y); auto.
  rewrite~ num_of_all_open_rec_mono.
  rewrite~ num_of_all_open_rec_mono.
  Omega.omega.
  apply notin_union.
  splits~.
  apply~ dnotin_fv_tt_open_inv. simpls~.
  apply~ dnotin_fv_tt_open_inv. simpls~.
  rewrite~ dopen_tt_rec_type_commu.
  pattern (dopen_tt_rec (S n) (dtyp_fvar y) (dopen_tt_rec 0 (dtyp_fvar x) B))
          at 1;
    rewrite~ dopen_tt_rec_type_commu.
Qed.

Lemma dtyp_less_precise_open: forall A B y t,
    y \notin dfv_tt A \u dfv_tt B ->
    dtyp_less_precise (A dopen_tt_var y)
                      (B dopen_tt_var y) ->
    dtype t ->
    dtyp_less_precise (dopen_tt A t)
                      (dopen_tt B t).
Proof.
  intros.
  apply* dtyp_less_precise_open'.
Qed.

Lemma dmatch_less_precise_input': forall m E A A1 A2 B,
    num_of_all A < m ->
    dmatch E A A1 A2 ->
    dtyp_less_precise B A ->
    exists B1 B2, dmatch E B B1 B2 /\ dtyp_less_precise B1 A1 /\ dtyp_less_precise B2 A2.
Proof.
  intro m. inductions m; introv lem. inversions lem.

  introv dm less. gen E A1 A2.
  inductions less; introv dm;
    simpls~; try(solve[inversions~ dm]).

  exists dtyp_unknown dtyp_unknown. splits~. constructor~.
  constructor~. apply(dmatch_regular_dtype dm H).
  constructor~. apply(dmatch_regular_dtype dm H).

  inversions dm.
  exists A1 A2. splits~. constructor~.

  clear H0.
  inversions dm.
  pick_fresh y.
  forwards ~ : H y.
  forwards ~ : dtyp_less_precise_open tau H0.
  forwards ~ : IHm H4 H3.
  rewrite~ num_of_all_open_mono. Omega.omega.
  destruct H5 as (C1 & C2 & [? [? ?]]).
  exists~ C1 C2. splits~.
  apply dmatch_all with tau; auto.
Qed.

Lemma dmatch_less_precise_input: forall E A A1 A2 B,
    dmatch E A A1 A2 ->
    dtyp_less_precise B A ->
    exists B1 B2, dmatch E B B1 B2 /\ dtyp_less_precise B1 A1 /\ dtyp_less_precise B2 A2.
Proof.
  intros. apply* dmatch_less_precise_input'.
Qed.

Lemma dtyp_less_precise_consist_same: forall A B1 B2,
    dtyp_less_precise B1 A ->
    dtyp_less_precise B2 A ->
    dconsist B1 B2.
Proof.
  introv la lb. gen B2. inductions la; introv lb.
  constructor~.
  inversions lb; constructor~.

  inversions lb. constructor~.
  constructor~.

  inversions lb. constructor~.
  constructor~.

  inversions lb. constructor~.
  apply dconsist_all.
  pick_fresh y.
  forwards ~ : H3 y.
  forwards ~ : H0 H1.
  forwards ~ : dconsist_close y H2.
  rewrite~ dopen_tt_close_fresh in H4.
  rewrite~ dopen_tt_close_fresh in H4.
Qed.

Lemma dtyp_less_precise_consist: forall A1 A2 B1 B2,
    dtyp_less_precise A1 A2 ->
    dtyp_less_precise B1 B2 ->
    dconsist A2 B2 ->
    dconsist A1 B1.
Proof.
  introv la. gen B1 B2. inductions la; introv lb con.
  constructor~.
  inversions con; inversions lb; constructor~.

  inversions~ con;
  inversions~ lb.

  inversions~ con; inversions~ lb.
  constructor~. apply* IHla1. apply* IHla2.
  constructor~. apply* IHla1. apply* IHla2.

  inversions~ con; inversions~ lb.
  constructor~.
  pick_fresh y.
  forwards ~ : H3 y.
  forwards ~ : H0 y H1.
  forwards ~ : dconsist_close y H2.
  rewrite~ dopen_tt_close_fresh in H4.
  rewrite~ dopen_tt_close_fresh in H4.

  constructor~.
  pick_fresh y.
  forwards ~ : H4 y.
  forwards ~ : H0 y H1.
  apply~ dconsist_open.
  forwards ~ : dconsist_close y H3.
  rewrite~ dopen_tt_close_fresh in H5.
  rewrite~ dopen_tt_close_fresh in H5.
Qed.

(** Properties for denv less precise *)

Lemma denv_less_precise_dokt: forall E F,
    denv_less_precise E F ->
    dokt E /\ dokt F.
Proof.
  introv de. inductions de; autos~.
  destruct IHde.
  split~; constructor~.
  destruct IHde.
  split~.
Qed.

Lemma denv_less_precise_dokt_l: forall E F,
    denv_less_precise E F ->
    dokt E.
Proof.
  applys denv_less_precise_dokt.
Qed.

Lemma denv_less_precise_dokt_r: forall E F,
    denv_less_precise E F ->
    dokt F.
Proof.
  applys denv_less_precise_dokt.
Qed.

Lemma denv_less_precise_binds : forall x A E F,
    binds x (dbind_typ A) E ->
    denv_less_precise F E ->
    exists B, binds x (dbind_typ B) F /\ dtyp_less_precise B A.
Proof.
  introv bd less. inductions less.
  exists A. splits~. apply~ dtyp_less_precise_refl.
  apply dwft_dtype with E; auto.
  apply* dwft_from_env_has_typ.

  apply binds_push_inv in bd. destruct bd as [[? ?] | [? ?]]; subst.
  inversions H5.
  exists A1. splits~.
  forwards ~ (C & [? ?]): IHless.
  exists C. splits~.

  apply binds_push_inv in bd. destruct bd as [[? ?] | [? ?]]; subst.
  inversions H2.
  forwards ~ (C & [? ?]): IHless.
  exists C. splits~.
Qed.

Lemma denv_more_precise_binds : forall x B E F,
    binds x (dbind_typ B) F ->
    denv_less_precise F E ->
    exists A, binds x (dbind_typ A) E /\ dtyp_less_precise B A.
Proof.
  introv bd less. inductions less.
  exists B. splits~. apply~ dtyp_less_precise_refl.
  apply dwft_dtype with E; auto.
  apply* dwft_from_env_has_typ.

  apply binds_push_inv in bd. destruct bd as [[? ?] | [? ?]]; subst.
  inversions H5.
  exists A2. splits~.
  forwards ~ (C & [? ?]): IHless.
  exists C. splits~.

  apply binds_push_inv in bd. destruct bd as [[? ?] | [? ?]]; subst.
  inversions H2.
  forwards ~ (C & [? ?]): IHless.
  exists C. splits~.
Qed.

Lemma denv_less_precise_binds_var : forall x A B E F,
    denv_less_precise F E ->
    binds x (dbind_typ A) E ->
    binds x (dbind_typ B) F ->
    dtyp_less_precise B A.
Proof.
  introv env be bf.
  inductions env; auto.
  forwards : binds_func be bf. inversions H0.
  apply~ dtyp_less_precise_refl.
  apply dwft_dtype with E; auto.
  apply* dwft_from_env_has_typ.

  tests: (x=x0).
  apply binds_push_eq_inv in be. inversions~ be.
  apply binds_push_eq_inv in bf. inversions~ bf.

  apply binds_push_neq_inv in be; auto.
  apply binds_push_neq_inv in bf; auto.

  tests: (x=x0).
  apply binds_push_eq_inv in be. inversions~ be.

  apply binds_push_neq_inv in be; auto.
  apply binds_push_neq_inv in bf; auto.
Qed.

Lemma denv_more_precise_binds_tvar : forall x E F,
    binds x dbind_tvar F ->
    denv_less_precise F E ->
    binds x dbind_tvar E.
Proof.
  introv bd less. inductions less; simpls~.
  tests : (x = x0).
  apply binds_push_eq_inv in bd. inversions bd.
  apply binds_push_neq_inv in bd; auto.
  tests : (x = x0).
  apply~ binds_push_eq.
  apply binds_push_neq_inv in bd; auto.
Qed.

Lemma denv_less_precise_binds_tvar : forall x E F,
    binds x dbind_tvar E ->
    denv_less_precise F E ->
    binds x dbind_tvar F.
Proof.
  introv bd less. inductions less; simpls~.
  tests : (x = x0).
  apply binds_push_eq_inv in bd. inversions bd.
  apply binds_push_neq_inv in bd; auto.
  tests : (x = x0).
  apply~ binds_push_eq.
  apply binds_push_neq_inv in bd; auto.
Qed.

(** dwft less precise *)

Lemma denv_less_precise_preserve_dwft: forall E F A,
    dwft E A ->
    denv_less_precise F E ->
    dwft F A.
Proof.
  introv wf less. gen F.
  inductions wf; introv less;
    inversions less; simpls~.
  constructor~. constructor~.
  apply denv_less_precise_dokt_l in H0. auto.

  constructor~. constructor~.
  apply denv_less_precise_dokt_l in H0. auto.

  tests : (x = x0).
  apply binds_push_eq_inv in H0. inversions H0.
  apply binds_push_neq_inv in H0; auto.
  forwards ~ : denv_less_precise_binds_tvar H0 H1.

  tests : (x = x0).
  constructor~.
  apply denv_less_precise_dokt_l in H1. auto.
  apply binds_push_neq_inv in H0; auto.
  forwards ~ : denv_less_precise_binds_tvar H0 H1.
  constructor~.
  apply denv_less_precise_dokt_l in H1. auto.

  constructor~. apply~ IHwf1. constructor~.
  apply~ IHwf2. constructor~.

  constructor~. apply~ IHwf1. constructor~.
  apply~ IHwf2. constructor~.

  apply_fresh dwft_all as x.
  apply~ H0.
  apply~ denv_less_precise_refl.

  apply_fresh dwft_all as x.
  apply~ H0. constructor~. constructor~.

  apply_fresh dwft_all as x.
  apply~ H0. constructor~. constructor~.
Qed.

Lemma dwft_dtyp_less_precise: forall E A B,
    dwft E A ->
    dtyp_less_precise B A ->
    dwft E B.
Proof.
  introv wf less.
  gen E; inductions less; introv wf; autos~.
  inversions wf. constructor~.
  inversions wf.
  apply_fresh dwft_all as x.
  apply~ H0.
Qed.

Lemma dwft_denv_less_precise: forall E A F,
    dwft E A ->
    denv_less_precise F E ->
    dwft F A.
Proof.
  introv wf less.
  gen F; inductions wf; introv less; autos~.
  constructor~.
  lets ~ : denv_less_precise_dokt_r less.
  apply* dok_from_okt.
  lets ~ : denv_less_precise_dokt_l less.

  constructor~.
  lets ~ : denv_less_precise_dokt_r less.
  apply* dok_from_okt.
  lets ~ : denv_less_precise_dokt_l less.

  constructor~.
  lets ~ : denv_less_precise_dokt_r less.
  apply* dok_from_okt.
  lets ~ : denv_less_precise_dokt_l less.

  lets ~ : denv_less_precise_binds_tvar H0 less.

  apply_fresh dwft_all as x.
  apply~ H0.
  constructor~.
Qed.

Lemma dwft_denv_more_precise: forall E A F,
    dwft F A ->
    denv_less_precise F E ->
    dwft E A.
Proof.
  introv wf less.
  gen E; inductions wf; introv less; autos~.
  constructor~.
  lets ~ : denv_less_precise_dokt_r less.
  constructor~.
  lets ~ : denv_less_precise_dokt_r less.

  constructor~.
  lets ~ : denv_less_precise_dokt_r less.
  lets ~ : denv_more_precise_binds_tvar H0 less.

  apply_fresh dwft_all as x.
  apply~ H0.
  constructor~.
Qed.

(** dconsub less precise *)

Lemma dconsub_dtyp_less_precise: forall A B A1 B1 E,
    dconsub E A B ->
    dtyp_less_precise A1 A ->
    dtyp_less_precise B1 B ->
    dconsub E A1 B1.
Proof.
  introv sub less1 less2.
  assert (dokt E). auto.
  assert (dwft E A1). apply dwft_dtyp_less_precise with A; auto.
  assert (dwft E B1). apply dwft_dtyp_less_precise with B; auto.
  gen A1 B1.
  inductions sub; introv less1 wf1 less2 wf2; simpls~;
  inversions less1;
  inversions less2; try(constructor~).

  inversions wf1. inversions wf2. apply~ IHsub1.
  inversions wf1. inversions wf2. apply~ IHsub2.

  apply dconsub_allL with tau; auto.
  apply~ IHsub.
  pick_fresh y. forwards ~ : H4 y.
  apply dtyp_less_precise_open with y; auto.
  apply* dwft_open.

  apply dconsub_allL with tau; auto.
  apply~ IHsub.
  pick_fresh y. forwards ~ : H4 y.
  apply dtyp_less_precise_open with y; auto.
  apply* dwft_open.

  apply dconsub_allL with tau; auto.
  apply~ IHsub.
  pick_fresh y. forwards ~ : H4 y.
  apply dtyp_less_precise_open with y; auto.
  apply* dwft_open.

  apply dconsub_allL with tau; auto.
  apply~ IHsub.
  pick_fresh y. forwards ~ : H4 y.
  apply dtyp_less_precise_open with y; auto.
  apply* dwft_open.
  apply_fresh dtyp_less_precise_all as x; auto.

  inversions wf2.
  apply_fresh dconsub_allR as x; auto.
  apply~ H0. apply* dwft_push.

  inversions wf2.
  apply_fresh dconsub_allR as x; auto.

  inversions wf2.
  apply_fresh dconsub_allR as x; auto.
  apply~ H0. apply* dwft_push.

  inversions wf2.
  apply_fresh dconsub_allR as x; auto.
  apply~ H0.
  apply_fresh dtyp_less_precise_all as x; auto.
  apply* dwft_push.
Qed.

Lemma dsub_dtyp_less_precise: forall A B A1 B1 E,
    dsub E A B ->
    dtyp_less_precise A1 A ->
    dtyp_less_precise B1 B ->
    dconsub E A1 B1.
Proof.
  introv sub less1 less2.
  assert (dokt E). auto.
  assert (dwft E A1). apply dwft_dtyp_less_precise with A; auto.
  assert (dwft E B1). apply dwft_dtyp_less_precise with B; auto.
  gen A1 B1.
  inductions sub; introv less1 wf1 less2 wf2; simpls~;
  inversions less1;
  inversions less2; try(constructor~).

  inversions wf1. inversions wf2. apply~ IHsub1.
  inversions wf1. inversions wf2. apply~ IHsub2.

  apply dconsub_allL with tau; auto.
  apply~ IHsub.
  pick_fresh y. forwards ~ : H4 y.
  apply dtyp_less_precise_open with y; auto.
  apply* dwft_open.

  apply dconsub_allL with tau; auto.
  apply~ IHsub.
  pick_fresh y. forwards ~ : H4 y.
  apply dtyp_less_precise_open with y; auto.
  apply* dwft_open.

  apply dconsub_allL with tau; auto.
  apply~ IHsub.
  pick_fresh y. forwards ~ : H4 y.
  apply dtyp_less_precise_open with y; auto.
  apply* dwft_open.

  apply dconsub_allL with tau; auto.
  apply~ IHsub.
  pick_fresh y. forwards ~ : H4 y.
  apply dtyp_less_precise_open with y; auto.
  apply* dwft_open.
  apply_fresh dtyp_less_precise_all as x; auto.

  inversions wf2.
  apply_fresh dconsub_allR as x; auto.
  apply~ H0. apply* dwft_push.

  inversions wf2.
  apply_fresh dconsub_allR as x; auto.

  inversions wf2.
  apply_fresh dconsub_allR as x; auto.
  apply~ H0. apply* dwft_push.

  inversions wf2.
  apply_fresh dconsub_allR as x; auto.
  apply~ H0.
  apply_fresh dtyp_less_precise_all as x; auto.
  apply* dwft_push.
Qed.

Lemma dconsub_denv_less_precise: forall E A B F,
    dconsub E A B ->
    denv_less_precise F E ->
    dconsub F A B.
Proof.
  introv sub less.
  gen F; inductions sub; introv less; autos~.
  constructor~.
  lets ~ : denv_less_precise_dokt_l less.

  constructor~.
  lets ~ : denv_less_precise_dokt_l less.
  lets ~ : denv_less_precise_binds_tvar H0 less.

  constructor~.
  lets ~ : denv_less_precise_dokt_l less.
  lets ~ : dwft_denv_less_precise H0 less.

  constructor~.
  lets ~ : denv_less_precise_dokt_l less.
  lets ~ : dwft_denv_less_precise H0 less.

  apply dconsub_allL with tau; auto.
  lets ~ : dwft_denv_less_precise H0 less.

  apply_fresh dconsub_allR as x; auto.
  apply~ H0.
  constructor~.
Qed.

(** dmatch less precise *)

Lemma dmatch_denv_less_precise: forall E F A B1 B2,
    dmatch E A B1 B2 ->
    denv_less_precise F E ->
    dmatch F A B1 B2.
Proof.
  introv mat less.
  gen F. inductions mat; introv less; simpls~; try(constructor~).
  apply dmatch_all with tau; auto.
  lets ~ : dwft_denv_less_precise H0 less.
Qed.

(** substitution  *)

Lemma dwft_rename_typ : forall E F z u A T,
    dwft (E & z ~: T & F) A ->
    dokt (E & u ~: T & F) ->
    dwft (E & u ~: T & F) A.
Proof.
  introv wf okt.
  inductions wf; simpls; auto.
  tests : (z = x).
  apply~ dwft_var.
  apply binds_middle_eq_inv in H0; auto.
  inversion H0.

  apply* dwft_var.
  forwards ~ : binds_remove H0.
  apply~ binds_weaken.

  apply~ dwft_arrow.
  apply~ IHwf1. apply~ IHwf2.

  apply_fresh dwft_all as x.
  forwards ~ : H0 x E (F & x ~tvar) z.
  rewrite~ concat_assoc.
  rewrite~ concat_assoc.
  rewrite concat_assoc in H1; auto.
Qed.

Hint Constructors dmatch.
Lemma dmatch_rename_typ : forall E F z u A A1 A2 T,
    dmatch (E & z ~: T & F) A A1 A2 ->
    dokt (E & u ~: T & F) ->
    dmatch (E & u ~: T & F) A A1 A2
.
Proof.
  introv mat okt.
  inductions mat; simpls; auto.
  apply dmatch_all with tau; auto.
  apply* dwft_rename_typ.
  apply~ IHmat.
Qed.

Hint Resolve dconsub_refl dwft_rename_typ.
Lemma dconsub_rename_typ : forall E F z u A1 A2 T,
    dconsub (E & z ~: T & F) A1 A2 ->
    dokt (E & u ~: T & F) ->
    dconsub (E & u ~: T & F) A1 A2
.
Proof.
  introv mat okt.
  inductions mat; simpls; auto.

  apply~ dconsub_refl.
  tests : (z = x).
  apply binds_middle_eq_inv in H0; auto.
  inversion H0.

  apply* dwft_var.
  forwards ~ : binds_remove H0.
  apply~ binds_weaken.

  apply~ dconsub_unknown_l.
  apply* dwft_rename_typ.

  apply~ dconsub_unknown_r.
  apply* dwft_rename_typ.

  constructor~.
  apply~ IHmat1. apply~ IHmat2.

  apply dconsub_allL with tau; auto.
  apply* dwft_rename_typ.
  apply~ IHmat.

  apply_fresh dconsub_allR as x; auto.
  rewrite <- concat_assoc.
  apply~ H0.
  rewrite~ concat_assoc.
  rewrite~ concat_assoc.
Qed.

Lemma dwft_subst_tvar : forall E F z u A,
  dwft (E & z ~tvar & F) A ->
  ok (E & u ~tvar & map (dsubst_tb z (dtyp_fvar u)) F) ->
  dwft (E & u ~tvar & map (dsubst_tb z (dtyp_fvar u)) F) (dsubst_tt z (dtyp_fvar u) A).
Proof.
  introv wf oke. inductions wf; simpls~; auto.

  case_var~; constructor~.
    apply~ binds_middle_eq.
      lets~ [? ?] : ok_middle_inv oke.
    lets [? | [[? [? _]] | [? [? ?]]]] : binds_middle_inv H0.
      apply binds_concat_right.
        unsimpl (dsubst_tb z (dtyp_fvar u) dbind_tvar).
        apply~ binds_map.
      apply C in H2. contradiction.
      apply~ binds_concat_left.
        tests : (x = u).
          apply~ binds_push_eq.
          apply~ binds_concat_left.

  apply_fresh dwft_all as x.
  forwards ~ : H0 x E (F & x ~tvar) z.
  rewrite~ concat_assoc.
  rewrite map_push.
  rewrite~ concat_assoc.
  rewrite map_push in H1.
  rewrite concat_assoc in H1. simpls.
  rewrite~ dsubst_tt_open_tt_var.
Qed.

Hint Constructors dmatch.
Lemma dmatch_subst_tvar: forall E F z A A1 A2 u,
  dmatch (E & z ~tvar & F) A A1 A2 ->
  dokt (E & u ~tvar & map (dsubst_tb z (dtyp_fvar u)) F) ->
  dmatch (E & u ~tvar & map (dsubst_tb z (dtyp_fvar u)) F)
     (dsubst_tt z (dtyp_fvar u) A) (dsubst_tt z (dtyp_fvar u) A1)
     (dsubst_tt z (dtyp_fvar u) A2).
Proof.
  introv mat oke. inductions mat; simpl; auto.
  apply dmatch_all with (dsubst_tt z (dtyp_fvar u) tau); auto.
  apply~ dsubst_mono.
  apply~ dwft_subst_tvar.
  rewrite~ <- dsubst_tt_open_tt.
Qed.

Hint Resolve dwft_subst_tvar.

Lemma dconsub_subst_tvar: forall E F z A1 A2 u,
  dconsub (E & z ~tvar & F) A1 A2 ->
  dokt (E & u ~tvar & map (dsubst_tb z (dtyp_fvar u)) F) ->
  dconsub (E & u ~tvar & map (dsubst_tb z (dtyp_fvar u)) F)
     (dsubst_tt z (dtyp_fvar u) A1)
     (dsubst_tt z (dtyp_fvar u) A2).
Proof.
  introv sub oke. inductions sub; autos~ dconsub_refl; simpls~.

  apply dconsub_allL with (dsubst_tt z (dtyp_fvar u) tau); auto.
  apply~ dsubst_mono.
  rewrite~ <- dsubst_tt_open_tt.

  apply_fresh dconsub_allR as x.
  forwards ~ : H0 x E (F & x ~tvar) z.
  rewrite~ concat_assoc.
  rewrite map_push. rewrite~ concat_assoc.
  rewrite map_push in H2. rewrite concat_assoc in H2.
  rewrite~ dsubst_tt_open_tt_var.
Qed.

Lemma dsub_subst_tvar: forall E F z A1 A2 u,
  dsub (E & z ~tvar & F) A1 A2 ->
  dokt (E & u ~tvar & map (dsubst_tb z (dtyp_fvar u)) F) ->
  dsub (E & u ~tvar & map (dsubst_tb z (dtyp_fvar u)) F)
     (dsubst_tt z (dtyp_fvar u) A1)
     (dsubst_tt z (dtyp_fvar u) A2).
Proof.
  introv sub oke. inductions sub; autos~ dsub_refl; simpls~.

  apply dsub_allL with (dsubst_tt z (dtyp_fvar u) tau); auto.
  apply~ dsubst_mono.
  rewrite~ <- dsubst_tt_open_tt.

  apply_fresh dsub_allR as x.
  forwards ~ : H0 x E (F & x ~tvar) z.
  rewrite~ concat_assoc.
  rewrite map_push. rewrite~ concat_assoc.
  rewrite map_push in H2. rewrite concat_assoc in H2.
  rewrite~ dsubst_tt_open_tt_var.
Qed.


Hint Extern 1 (dtype ?E) =>
  match goal with
  | H: dtyp_static _ |- _ => apply (dtyp_static_dtype H)
  end.

Lemma dtyp_less_precise_static_exist : forall E A,
    dwft E A ->
    exists B,
      dtyp_static B
      /\ dtyp_less_precise A B
      /\ dwft E B.
Proof.
  introv ty. inductions ty.
  exists dtyp_nat. splits~.
  exists dtyp_nat. splits~.
  exists (dtyp_fvar x). splits~.

  destruct IHty1 as (B1 & [? [? ?]]).
  destruct IHty2 as (B2 & [? [? ?]]).
  exists (dtyp_arrow B1 B2). splits~.

  pick_fresh y.
  forwards ~ (B & [? [? ?]]) : H0 y.
  exists (dtyp_all (dclose_tt y B)). splits~.
    apply_fresh dtyp_static_all as x.
    apply dtyp_static_open with (dtyp_fvar y); auto.
    rewrite~ <- dclose_tt_open_var.
  apply dtyp_less_precise'_precise.
  apply dtyp_less_precise'_all with y; auto.
  assert (y \notin dfv_tt (dclose_tt y B)).
    apply~ dclose_tt_fresh.
  auto.
  rewrite~ <- dclose_tt_open_var.
  apply~ dtyp_less_precise_precise'.

  apply_fresh dwft_all as x.
  assert (dwft (E & y ~tvar & empty) B) by rewrite~ concat_empty_r.
  apply dwft_subst_tvar  with (u:=x) in H4.
  rewrite map_empty in H4. clean_empty H4.
  unfold dopen_tt, dclose_tt.
  rewrite~ dclose_tt_open_subst.
  rewrite~ map_empty. rewrite~ concat_empty_r.
  constructor~.
  apply dwft_ok in H3.
  auto.
Qed.

Lemma dconsist_directed : forall E A B,
    dconsist A B ->
    dwft E A ->
    dwft E B ->
    exists C, dtyp_static C /\
         dwft E C /\
         dtyp_less_precise A C /\
         dtyp_less_precise B C.
Proof.
  introv con wfa wfb. gen B. inductions wfa; introv con wfb.

  exists dtyp_nat. splits~.
  inversions~ con.

  lets~ (C & [? [? ?]]) : dtyp_less_precise_static_exist E B.
  exists C. splits~.

  exists (dtyp_fvar x). splits~.
  inversions~ con.

  inversions con.
    lets~ (B & [? [? ?]]) : dtyp_less_precise_static_exist E (dtyp_arrow A1 A2).
       exists B. splits~.
    lets~ (B & [? [? ?]]) : dtyp_less_precise_static_exist E (dtyp_arrow A1 A2).
       exists B. splits~.
    inversions wfb.
      forwards ~ (C1 & [? [? [? ?]]]) : IHwfa1 B1.
      forwards ~ (C2 & [? [? [? ?]]]) : IHwfa2 B2.
  exists (dtyp_arrow C1 C2). splits~.

  inversions con.
    lets~ (B & [? [? ?]]) : dtyp_less_precise_static_exist E (dtyp_all A).
       exists B. splits~.
    lets~ (B & [? [? ?]]) : dtyp_less_precise_static_exist E (dtyp_all A).
       apply_fresh dwft_all as x. auto.
       exists B. splits~.
    inversions wfb.
      pick_fresh x.
      forwards ~ (C & [? [? [? ?]]]) : H0 x (B0 dopen_tt_var x).
        apply~ dconsist_open.
      exists (dtyp_all (dclose_tt x C)). splits~.
        apply_fresh dtyp_static_all as x.
        apply dtyp_static_open with (dtyp_fvar x); auto.
        rewrite~ <- dclose_tt_open_var.
        apply_fresh dwft_all as y.
        assert (dwft (E & x ~tvar & empty) C) by rewrite~ concat_empty_r.
          apply dwft_subst_tvar with (u:=y) in H7; auto.
            rewrite map_empty in H7.
            clean_empty H7.
            unfold dclose_tt, dopen_tt.
            rewrite~ dclose_tt_open_subst.
            rewrite map_empty. rewrite concat_empty_r. constructor~.
            apply dwft_ok in H3. auto.
        apply dtyp_less_precise'_precise.
          apply dtyp_less_precise'_all with x; auto.
          apply notin_union; splits~. apply~ dclose_tt_fresh.
          rewrite~ <- dclose_tt_open_var.
          apply* dtyp_less_precise_precise'.
        apply dtyp_less_precise'_precise.
          apply dtyp_less_precise'_all with x; auto.
          apply notin_union; splits~. apply~ dclose_tt_fresh.
          rewrite~ <- dclose_tt_open_var.
          apply* dtyp_less_precise_precise'.
Qed.

Lemma dconsist_directed_reserse : forall A B C,
    dtyp_less_precise A C ->
    dtyp_less_precise B C ->
    dconsist A B.
Proof.
  introv lea leb. gen B. inductions lea; introv leb; inversions leb; simpls~.

  pick_fresh x.
  forwards ~ : H3 x.
  forwards ~ : H0 H1.
  apply dconsist_close with (y :=x) in H2.
  rewrite dopen_tt_close_fresh in H2; auto.
  rewrite dopen_tt_close_fresh in H2; auto.
Qed.


Lemma dsub_dtyp_less_precise_static: forall A B A1 B1 E,
    dsub E A B ->
    dtyp_static A ->
    dtyp_static B ->
    dtyp_less_precise A1 A ->
    dtyp_less_precise B1 B ->
    dconsub E A1 B1.
Proof.
  introv sub ta tb less1 less2.
  assert (dokt E). auto.
  assert (dwft E A1). apply dwft_dtyp_less_precise with A; auto.
  assert (dwft E B1). apply dwft_dtyp_less_precise with B; auto.
  gen A1 B1.
  inductions sub; introv less1 wf1 less2 wf2; simpls~;
  inversions less1;
  inversions less2; try(constructor~).

  inversions wf1. inversions wf2. inversions ta. inversions tb.
  apply~ IHsub1.
  inversions wf1. inversions wf2. inversions ta. inversions tb.
  apply~ IHsub2.

  apply dconsub_allL with tau; auto.
  apply~ IHsub.
  inversions ta.
    pick_fresh y. apply dtyp_static_open with (dtyp_fvar y); auto.
    apply~ dtyp_mono_static.
  pick_fresh y. forwards ~ : H4 y.
  apply dtyp_less_precise_open with y; auto.
  apply* dwft_open.

  apply dconsub_allL with tau; auto.
  apply~ IHsub.
  inversions ta.
    pick_fresh y. apply dtyp_static_open with (dtyp_fvar y); auto.
    apply~ dtyp_mono_static.
  pick_fresh y. forwards ~ : H4 y.
  apply dtyp_less_precise_open with y; auto.
  apply* dwft_open.

  apply dconsub_allL with tau; auto.
  apply~ IHsub.
  inversions ta.
    pick_fresh y. apply dtyp_static_open with (dtyp_fvar y); auto.
    apply~ dtyp_mono_static.
  pick_fresh y. forwards ~ : H4 y.
  apply dtyp_less_precise_open with y; auto.
  apply* dwft_open.

  apply dconsub_allL with tau; auto.
  apply~ IHsub.
  inversions ta.
    pick_fresh y. apply dtyp_static_open with (dtyp_fvar y); auto.
    apply~ dtyp_mono_static.
  pick_fresh y. forwards ~ : H4 y.
  apply dtyp_less_precise_open with y; auto.
  apply* dwft_open.
  apply_fresh dtyp_less_precise_all as x; auto.

  inversions tb. inversions wf2.
  apply_fresh dconsub_allR as x; auto.
  apply~ H0. apply* dwft_push.

  inversions tb. inversions wf2.
  apply_fresh dconsub_allR as x; auto.

  inversions tb. inversions wf2.
  apply_fresh dconsub_allR as x; auto.
  apply~ H0. apply* dwft_push.

  inversions tb. inversions wf2.
  apply_fresh dconsub_allR as x; auto.
  apply~ H0.
  apply_fresh dtyp_less_precise_all as x; auto.
  apply* dwft_push.
Qed.