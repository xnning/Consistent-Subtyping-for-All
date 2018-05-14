Set Implicit Arguments.
Require Import TLC.LibLN.
Require Import DeclDef.
Require Import PBCDef DeclInfra PBCInfra.
Require Import DeclProp.

Inductive d2ptyping : denv -> dtrm -> dtyp -> ptrm -> Prop :=
  | d2ptyping_var : forall E x T,
      dokt E ->
      binds x (dbind_typ T) E ->
      d2ptyping E (dtrm_fvar x) T (ptrm_fvar x)
  | d2ptyping_nat : forall E i,
      dokt E ->
      d2ptyping E (dtrm_nat i) (dtyp_nat) (ptrm_nat i)
  | d2ptyping_absann : forall L E A B e s,
      dwft empty A ->
      (forall x, x \notin L ->
            d2ptyping (E & x ~: A) (e dopen_ee_var x) B (s popen_ee_var x)) ->
      d2ptyping E (dtrm_absann A e) (dtyp_arrow A B) (ptrm_absann A s)
  | d2ptyping_app : forall E e1 e2 A A1 A2 A3 s1 s2,
      d2ptyping E e1 A s1 ->
      dmatch E A A1 A2 ->
      d2ptyping E e2 A3 s2 ->
      dconsub E A3 A1 ->
      d2ptyping E (dtrm_app e1 e2) A2
                  (ptrm_app (ptrm_cast A (dtyp_arrow A1 A2) s1)
                            (ptrm_cast A3 A1 s2))
  | d2ptyping_abs : forall L E A B e s,
      dtyp_mono A ->
      (forall x, x \notin L ->
            d2ptyping (E & x ~: A) (e dopen_ee_var x) B (s popen_ee_var x)) ->
      d2ptyping E (dtrm_abs e) (dtyp_arrow A B) (ptrm_absann A s)
  | d2ptyping_gen : forall L E A e s,
      (forall a, a \notin L ->
            d2ptyping (E & a ~tvar) e (A dopen_tt_var a) (s popen_te_var a)) ->
      d2ptyping E e (dtyp_all A) (ptrm_tabs s)
  | d2ptyping_let : forall L E A B e1 e2 s1 s2,
      d2ptyping E e1 A s1 ->
      (forall x, x \notin L ->
            d2ptyping (E & x ~: A) (e2 dopen_ee_var x) B (s2 popen_ee_var x)) ->
      d2ptyping E (dtrm_let e1 e2) B (ptrm_app (ptrm_absann A s2) s1)
.

Hint Constructors dtyping ptyping d2ptyping.

Lemma d2ptyping_dtyping : forall E e T s,
  d2ptyping E e T s -> dtyping E e T.
Proof.
  introv ty. inductions ty; autos*.
Qed.

Lemma d2ptyping_regular : forall E e T f,
  d2ptyping E e T f -> dokt E /\ dterm e /\ dwft E T.
Proof.
  introv ty. lets: d2ptyping_dtyping ty.
  lets ~ [? ?]: dtyping_regular H.
Qed.

Hint Resolve d2ptyping_regular.

Hint Extern 1 (dokt ?E) =>
  match goal with
  | H: d2ptyping _ _ _ _ |- _ => apply (proj31 (d2ptyping_regular H))
  end.

Hint Extern 1 (dterm ?E) =>
  match goal with
  | H: d2ptyping _ _ _ _ |- _ => apply (proj32 (d2ptyping_regular H))
  end.

Hint Extern 1 (dwft ?E ?t) =>
  match goal with
  | H: d2ptyping _ _ _ _ |- _ => apply (proj33 (d2ptyping_regular H))
  end.

Lemma d2ptyping_term : forall E e T s,
  d2ptyping E e T s -> pterm s.
Proof.
  introv ty. inductions ty; autos*.

  forwards ~ [? ?] : dmatch_regular H.
  forwards ~ [? [? ?]] : dconsub_regular H0.
  constructor~. constructor~.
  apply* dwft_dtype.

  apply_fresh pterm_absann as x; auto.
  apply* dtyp_mono_dtype.
Qed.

Hint Resolve d2ptyping_term.

Hint Constructors pcompatible.

Lemma pcompatible_dsubst_unknown': forall m A B x,
    num_of_all A + num_of_all B < m ->
    pcompatible A B ->
    pcompatible (dsubst_tt x dtyp_unknown A) B /\
    pcompatible A (dsubst_tt x dtyp_unknown B).

Proof.
  intro m.
  inductions m; introv lem.
  inversion lem.

  introv com.
  inductions com; introv; simpls~.

  (* *)
  inductions A; simpls~. splits~.
  constructor~. apply IHA1. Omega.omega.
  apply IHA2. Omega.omega.
  constructor~. apply IHA1. Omega.omega.
  apply IHA2. Omega.omega.

  case_var~.

  splits~.
  apply_fresh pcompatible_allR as x.
  apply pcompatible_allL.
  assert (dsubst_tt x dtyp_unknown dtyp_unknown = dtyp_unknown). simpls~.
  pattern dtyp_unknown at 2; rewrite <- H.
  rewrite~ <- dsubst_tt_open_tt.
  apply~ IHm.
  rewrite~ num_of_all_open_unknown.
  rewrite~ num_of_all_open_mono. Omega.omega.
  rewrite dsubst_tt_intro with y A dtyp_unknown; auto.
  apply~ IHm. repeat rewrite~ num_of_all_open_mono. Omega.omega.

  apply_fresh pcompatible_allR as x.
  apply pcompatible_allL.
  assert (dsubst_tt x dtyp_unknown (dtyp_fvar y) = (dtyp_fvar y)). simpls~. case_var~.
  pattern dtyp_unknown at 2; rewrite <- H.
  rewrite~ <- dsubst_tt_open_tt.
  apply~ IHm.
  rewrite~ num_of_all_open_unknown.
  rewrite~ num_of_all_open_mono. Omega.omega.
  rewrite dsubst_tt_intro with y A dtyp_unknown; auto.
  apply~ IHm. rewrite~ num_of_all_open_mono. Omega.omega.

  (* *)
  splits~.
  constructor~. apply IHcom1. Omega.omega.
  apply IHcom2. Omega.omega.
  constructor~. apply IHcom1. Omega.omega.
  apply IHcom2. Omega.omega.

  (* *)
  splits~.
  apply_fresh pcompatible_allR as x.
  apply~ H0.
  rewrite~ num_of_all_open_mono. Omega.omega.
  apply_fresh pcompatible_allR as x.
  assert (dsubst_tt x dtyp_unknown (dtyp_fvar y) = (dtyp_fvar y)). simpls~. case_var~.
  rewrite <- H1.
  rewrite~ <- dsubst_tt_open_tt.
  apply~ H0.
  rewrite~ num_of_all_open_mono. Omega.omega.

  (* *)
  splits~.
  apply pcompatible_allL.
  assert (dsubst_tt x dtyp_unknown dtyp_unknown = dtyp_unknown). simpls~.
  pattern dtyp_unknown at 2; rewrite <- H.
  rewrite~ <- dsubst_tt_open_tt.
  apply~ IHcom.
  rewrite~ num_of_all_open_unknown. Omega.omega.

  apply pcompatible_allL.
  apply~ IHm.
  rewrite~ num_of_all_open_unknown. Omega.omega.
Qed.

Lemma pcompatible_dsubst_unknown : forall A B x,
    pcompatible A B ->
    pcompatible (dsubst_tt x dtyp_unknown A) B /\
    pcompatible A (dsubst_tt x dtyp_unknown B)
.
Proof.
  intros.
  apply* pcompatible_dsubst_unknown'.
Qed.

Lemma pcompatible_dopen_rec_unknown_self': forall m A B k,
    num_of_all A < m ->
    dtype B ->
    pcompatible (dopen_tt_rec k dtyp_unknown A) (dopen_tt_rec k B A) /\
    pcompatible (dopen_tt_rec k B A) (dopen_tt_rec k dtyp_unknown A).
Proof.
  unfolds dopen_tt. intros m.
  inductions m; introv lem.
  inversions lem.

  gen k.
  inductions A; introv ty; simpls~.

  (* *)
  splits~.
  constructor~. apply~ IHA1. Omega.omega.
  apply~ IHA2. Omega.omega.

  constructor~. apply~ IHA1. Omega.omega.
  apply~ IHA2. Omega.omega.

  (* *)
  splits~;
  case_nat~.

  (* *)
  splits~.

  apply_fresh pcompatible_allR as x.
  apply pcompatible_allL.
  rewrite dsubst_tt_intro with x (dopen_tt_rec (S k) dtyp_unknown A) dtyp_unknown; auto.
  apply~ pcompatible_dsubst_unknown.
  unfolds dopen_tt.
  rewrite~ dopen_tt_rec_type_commu.
  pattern (dopen_tt_rec 0 (dtyp_fvar x)
        (dopen_tt_rec (S k) B A)) at 1;
  rewrite~ dopen_tt_rec_type_commu.
  apply~ IHm. rewrite~ num_of_all_open_rec_mono. Omega.omega.
  apply~ dnotin_fv_tt_open_inv. simpls~.

  apply_fresh pcompatible_allR as x.
  apply pcompatible_allL.
  rewrite dsubst_tt_intro with x (dopen_tt_rec (S k) B A) dtyp_unknown; auto.
  apply~ pcompatible_dsubst_unknown.
  unfolds dopen_tt.
  rewrite~ dopen_tt_rec_type_commu.
  pattern (dopen_tt_rec 0 (dtyp_fvar x)
        (dopen_tt_rec (S k) dtyp_unknown A)) at 1;
  rewrite~ dopen_tt_rec_type_commu.
  apply~ IHm. rewrite~ num_of_all_open_rec_mono. Omega.omega.
  apply~ dnotin_fv_tt_open_inv.
Qed.

Lemma pcompatible_dopen_rec_unknown_self: forall A B k,
    dtype B ->
    pcompatible (dopen_tt_rec k dtyp_unknown A) (dopen_tt_rec k B A) /\
    pcompatible (dopen_tt_rec k B A) (dopen_tt_rec k dtyp_unknown A).
Proof.
  intros. apply* pcompatible_dopen_rec_unknown_self'.
Qed.

Lemma pcompatible_dopen_unknown_self: forall A B,
    dtype B ->
    pcompatible (dopen_tt A dtyp_unknown) (dopen_tt A B) /\
    pcompatible (dopen_tt A B) (dopen_tt A dtyp_unknown).
Proof.
  intros. apply* pcompatible_dopen_rec_unknown_self'.
Qed.

Fixpoint dtyp_len (t: dtyp) : nat :=
  match t with
  | dtyp_nat => 1
  | dtyp_unknown => 1
  | dtyp_fvar _ => 1
  | dtyp_bvar _ => 1
  | dtyp_arrow t1 t2 =>
      1 + dtyp_len t1 + dtyp_len t2
  | dtyp_all t1 =>
    1 + dtyp_len t1
  end.

Lemma dtyp_len_open_tt_fvar: forall S U k,
    dtyp_len (dopen_tt_rec k (dtyp_fvar U) S) = dtyp_len S.
Proof.
  induction S; introv; simpls~.
  case_nat~.
Qed.

Lemma dtyp_len_open_tt_unknown: forall S k,
    dtyp_len (dopen_tt_rec k dtyp_unknown S) = dtyp_len S.
Proof.
  induction S; introv; simpls~.
  case_nat~.
Qed.

Lemma pcompatible_dopen_unknown': forall m n A B C,
    num_of_all A + num_of_all B < m ->
    dtyp_len A + dtyp_len B < n ->
    dtype C ->
    (pcompatible (dopen_tt A C) B ->
     pcompatible (dopen_tt A dtyp_unknown) B) /\
    (pcompatible A (dopen_tt B C) ->
     pcompatible A (dopen_tt B dtyp_unknown)).
Proof.
  unfolds dopen_tt. generalize 0.
  intros n m. gen n. inductions m; introv lem.
  inversion lem.

  gen A B C n.
  inductions n0; introv lem len.
  inversions len.

  introv ty. splits~.

  (* left *)
  introv com. inductions com; simpls~.
  apply~ pcompatible_dopen_rec_unknown_self.

  destruct A; unfolds dopen_tt; simpls~; try(solve[inversions~ x]).
  case_nat~.

  destruct A; unfolds dopen_tt; simpls~; try(solve[inversions~ x]).
  inversions x. constructor~.
  clear IHcom1 IHcom2.
  apply IHn0 with C; auto. Omega.omega. Omega.omega.
  apply IHcom2 with C; auto. Omega.omega. Omega.omega.
  case_nat~.

  apply_fresh pcompatible_allR as x.
  apply H0 with (C0:=C); auto. rewrite~ num_of_all_open_mono. Omega.omega.
  unfold dopen_tt. rewrite dtyp_len_open_tt_fvar.
  Omega.omega.

  destruct A; unfolds dopen_tt; simpls~; try(solve[inversions~ x]).
  case_nat~.
  inversions~ x.
  apply~ pcompatible_allL.
  rewrite dopen_tt_rec_type_commu in com; auto.
  unfolds dopen_tt. rewrite~ dopen_tt_rec_type_commu.
  clear IHcom.
  forwards ~ : IHm (S n) (dopen_tt_rec 0 dtyp_unknown A) B C.
  rewrite num_of_all_open_rec_unknown. Omega.omega.
  apply~ H.

  (* right *)
  introv com. inductions com; simpls~.
  apply~ pcompatible_dopen_rec_unknown_self.

  destruct B; unfolds dopen_tt; simpls~; try(solve[inversions~ x]).
  case_nat~.

  destruct B; unfolds dopen_tt; simpls~; try(solve[inversions~ x]).
  inversions x. constructor~.
  clear IHcom1 IHcom2.
  apply IHn0 with C; auto. Omega.omega. Omega.omega.
  apply IHcom2 with C; auto. Omega.omega. Omega.omega.
  case_nat~.

  destruct B; unfolds dopen_tt; simpls~; try(solve[inversions~ x]).
  case_nat~.
  inversions~ x.
  apply_fresh pcompatible_allR as x.
  clear H0.
  unfolds dopen_tt. rewrite~ dopen_tt_rec_type_commu.
  forwards ~ : IHm (S n) A (dopen_tt_rec 0 (dtyp_fvar x) B) C.
  rewrite~ num_of_all_open_rec_mono. Omega.omega.
  apply~ H0.
  rewrite~ dopen_tt_rec_type_commu.

  apply pcompatible_allL.
  apply IHcom with (C0:=C); auto.
  rewrite~ num_of_all_open_unknown. Omega.omega.
  unfold dopen_tt. rewrite~ dtyp_len_open_tt_unknown. Omega.omega.
Qed.

Lemma pcompatible_dopen_unknown_l: forall A B C,
    dtype C ->
    pcompatible (dopen_tt A C) B ->
    pcompatible (dopen_tt A dtyp_unknown) B.
Proof.
  intros. unfolds dopen_tt.
  forwards ~ [? ?] : pcompatible_dopen_unknown' (1 + num_of_all A + num_of_all B) A B C.
Qed.

Lemma pcompatible_dopen_unknown_r: forall A B C,
    dtype C ->
    pcompatible A (dopen_tt B C) ->
    pcompatible A (dopen_tt B dtyp_unknown).
Proof.
  intros. unfolds dopen_tt.
  forwards ~ [? ?] : pcompatible_dopen_unknown' (1 + num_of_all A + num_of_all B) A B C.
Qed.

Lemma dmatch_pcompatible: forall E A1 A2 A,
    dmatch E A A1 A2 ->
    pcompatible A (dtyp_arrow A1 A2).
Proof.
  introv mat. inductions mat; simpls~.
  apply pcompatible_allL.

  apply pcompatible_dopen_unknown_l with tau; auto.
Qed.

Lemma dconsub_pcompatible: forall E A1 A2,
    dconsub E A1 A2 ->
    pcompatible A1 A2.
Proof.
  introv cons. inductions cons; simpls~.
  constructor~.

  apply pcompatible_dopen_unknown_l with tau; auto.

  apply_fresh pcompatible_allR as x.
  apply~ H0.
Qed.

Lemma d2ptyping_type : forall E e T s,
  d2ptyping E e T s -> ptyping E s T.
Proof.
  introv ty. inductions ty; autos*.

  apply ptyping_app with A1; auto.
  apply~ ptyping_cast. constructor~.
  forwards ~ [? ?] : dmatch_regular H.

  apply* dmatch_pcompatible.

  apply~ ptyping_cast.
  apply* dconsub_pcompatible.
Qed.

(** For proving dtyping_d2ptyping *)

Inductive d2ptyping' : denv -> dtrm -> dtyp -> ptrm -> Prop :=
  | d2ptyping'_var : forall E x T,
      dokt E ->
      binds x (dbind_typ T) E ->
      d2ptyping' E (dtrm_fvar x) T (ptrm_fvar x)
  | d2ptyping'_nat : forall E i,
      dokt E ->
      d2ptyping' E (dtrm_nat i) (dtyp_nat) (ptrm_nat i)
  | d2ptyping'_absann : forall x E A B e s,
      dwft empty A ->
      x \notin (dom E \u dfv_ee e \u pfv_ee s) ->
      d2ptyping' (E & x ~: A) (e dopen_ee_var x) B (s popen_ee_var x) ->
      d2ptyping' E (dtrm_absann A e) (dtyp_arrow A B) (ptrm_absann A s)
  | d2ptyping'_app : forall E e1 e2 A A1 A2 A3 s1 s2,
      d2ptyping' E e1 A s1 ->
      dmatch E A A1 A2 ->
      d2ptyping' E e2 A3 s2 ->
      dconsub E A3 A1 ->
      d2ptyping' E (dtrm_app e1 e2) A2
                  (ptrm_app (ptrm_cast A (dtyp_arrow A1 A2) s1)
                            (ptrm_cast A3 A1 s2))
  | d2ptyping'_abs : forall x E A B e s,
      x \notin (dom E \u dfv_ee e \u pfv_ee s) ->
      dtyp_mono A ->
      d2ptyping' (E & x ~: A) (e dopen_ee_var x) B (s popen_ee_var x) ->
      d2ptyping' E (dtrm_abs e) (dtyp_arrow A B) (ptrm_absann A s)
  | d2ptyping'_gen : forall a E A e s,
      a \notin (dom E \u dfv_tt A \u pfv_te s) ->
      d2ptyping' (E & a ~tvar) e (A dopen_tt_var a) (s popen_te_var a) ->
      d2ptyping' E e (dtyp_all A) (ptrm_tabs s)
  | d2ptyping'_let : forall x E A B e1 e2 s1 s2,
      x \notin (dom E \u dfv_ee e2 \u pfv_ee s2) ->
      d2ptyping' E e1 A s1 ->
      d2ptyping' (E & x ~: A) (e2 dopen_ee_var x) B (s2 popen_ee_var x) ->
      d2ptyping' E (dtrm_let e1 e2) B (ptrm_app (ptrm_absann A s2) s1)
.

Hint Constructors d2ptyping'.
Lemma d2ptyping_d2ctyping': forall E e t f,
    d2ptyping E e t f -> d2ptyping' E e t f.
Proof.
  induction 1; autos*.
  pick_fresh x.
  apply d2ptyping'_absann with x; auto.
  pick_fresh x.
  apply d2ptyping'_abs with x; auto.
  pick_fresh x.
  apply d2ptyping'_gen with x; auto.
  pick_fresh x.
  apply d2ptyping'_let with x; auto.
Qed.

Lemma d2ptyping_subst : forall E F t T z u U f,
    d2ptyping (E & z ~: U & F) t T f ->
    dokt (E & u ~: U & F) ->
    d2ptyping (E & u ~: U & F) (dsubst_ee z (dtrm_fvar u) t) T
              (psubst_ee z (ptrm_fvar u) f) .
Proof.
  introv typt. inductions typt; introv okt; simpl; f_equal~.
  case_var*.
    binds_mid~.
    apply d2ptyping_var; autos*.
    inversions TEMP.
    apply~ binds_middle_eq.
    lets: dok_from_okt okt.
    lets ~ : ok_middle_inv_r H0.

    apply* d2ptyping_var.
    forwards ~ : binds_remove H0.
    apply~ binds_weaken.

  apply_fresh d2ptyping_absann as x; auto.
  specializes H1 x E (F & x ~: A) z U.
  forwards * : H1.
  rewrite* concat_assoc.
  rewrite~ concat_assoc.
  specializes H0 x. forwards ~ : H0.
  lets [? _]: d2ptyping_regular H2.
  constructor~. apply dokt_push_typ_inv in H3. apply* dwft_rename_typ.
  rewrite concat_assoc in H2.
  rewrite* dsubst_ee_open_ee_var.
  rewrite* psubst_ee_open_ee_var.

  apply~ d2ptyping_app.
  apply* dmatch_rename_typ.
  apply* dconsub_rename_typ.

  apply_fresh d2ptyping_abs as x; auto.
  specializes H1 x E (F & x ~: A) z U.
  forwards * : H1.
  rewrite* concat_assoc.
  rewrite~ concat_assoc.
  specializes H0 x. forwards ~ : H0.
  lets [? _]: d2ptyping_regular H2.
  constructor~. apply dokt_push_typ_inv in H3. apply* dwft_rename_typ.
  rewrite concat_assoc in H2.
  rewrite* dsubst_ee_open_ee_var.
  rewrite* psubst_ee_open_ee_var.

  apply_fresh d2ptyping_gen as x; auto.
  specializes H0 x E (F & x ~tvar) z U.
  forwards * : H0.
  rewrite* concat_assoc.
  rewrite~ concat_assoc.
  rewrite concat_assoc in H1.
  rewrite* psubst_ee_open_te_var.
  
  apply_fresh d2ptyping_let as x; auto.
  specializes H0 x E (F & x ~: A) z U.
  forwards * : H0.
  rewrite* concat_assoc.
  rewrite~ concat_assoc.
  specializes H x. forwards ~ : H.
  lets [? _]: d2ptyping_regular H1.
  constructor~. apply dokt_push_typ_inv in H2. apply* dwft_rename_typ.
  rewrite concat_assoc in H1.
  rewrite* dsubst_ee_open_ee_var.
  rewrite* psubst_ee_open_ee_var.
Qed.

Lemma psubst_ee_same: forall y f,
    (psubst_ee y (ptrm_fvar y) f) = f.
Proof.
  inductions f; simpls; autos*; f_equal *.
  case_var*.
Qed.

Lemma d2ptyping_rename : forall x y E t S f V,
  d2ptyping (E & x ~: V) (S dopen_ee_var x) t f ->
  x \notin dom E \u dfv_ee S ->
  y \notin dom E \u dfv_ee S ->
  d2ptyping (E & y ~: V) (S dopen_ee_var y) t (psubst_ee x (ptrm_fvar y) f).
Proof.
  introv Typx Frx Fry.
  tests: (x = y). rewrite* psubst_ee_same.
  rewrite~ (@dsubst_ee_intro x).
  assert  (d2ptyping (E & y ~: V & empty) (dsubst_ee x (dtrm_fvar y) (S dopen_ee_var x)) t (psubst_ee x (ptrm_fvar y) f)).
  apply d2ptyping_subst.
  rewrite~ concat_empty_r.
  rewrite~ concat_empty_r.
  apply~ dokt_typ.
  lets [? ?]: d2ptyping_regular Typx.
  lets~ : dokt_concat_left_inv H.
  lets [? [? ?]]: d2ptyping_regular Typx.
  apply dokt_push_typ_inv in H. auto.

  rewrite~ concat_empty_r in H.
Qed.

Lemma d2ptyping_subst_tvar : forall E F t T z u f,
    d2ptyping (E & z ~tvar & F) t T f ->
    dokt (E & u ~tvar & map (dsubst_tb z (dtyp_fvar u)) F) ->
    d2ptyping (E & u ~tvar & map (dsubst_tb z (dtyp_fvar u)) F)
              t (dsubst_tt z (dtyp_fvar u) T)
              (psubst_te z (dtyp_fvar u) f) .
Proof.
  introv typt. inductions typt; introv okt; simpl; f_equal~.

  apply d2ptyping_var; autos*.
   destruct (binds_concat_inv H0) as [?|[? ?]].
       apply~ binds_concat_right.
       unsimpl (dsubst_tb z (dtyp_fvar u) (dbind_typ T)).
       apply~ binds_map.
   destruct (binds_push_inv H2) as [[? ?]|[? ?]].
       false~.
       apply~ binds_concat_left.
       apply~ binds_concat_left.
       rewrite~ dsubst_tt_fresh.
       apply dwft_notin_env with E; auto.
       apply* dwft_from_env_has_typ.
       do 2 apply dokt_concat_left_inv in H. auto.
       apply dokt_concat_left_inv in H.
       apply dokt_push_inv in H. destruct~ H.
       introv neq. simpl_dom. rewrite in_singleton in neq.
       subst.
       apply dokt_concat_left_inv in okt.
       apply dokt_push_inv in okt. destruct~ okt.
       apply binds_fresh_inv in H4; auto.

  assert (I: dsubst_tt z (dtyp_fvar u) A = A).
    apply dsubst_tt_fresh.
    apply~ dwft_notin_env; auto.
  rewrite I.
  apply_fresh d2ptyping_absann as x; auto.
  forwards ~ : H1 x E (F & x ~: A) z.
  rewrite~ concat_assoc.
  rewrite map_push.
  rewrite concat_assoc.
  constructor~.
  apply~ dwft_subst_tvar.
  forwards ~ : H0 x.
  lets [? _]: d2ptyping_regular H2.
  apply* dokt_push_typ_inv.
  rewrite map_push in H2.
  rewrite concat_assoc in H2; auto.
  simpl in H2. rewrite I in H2.
  rewrite* psubst_te_open_ee_var.

  apply~ d2ptyping_app.
  forwards ~ : IHtypt1.
  apply~ dmatch_subst_tvar.
  apply~ dconsub_subst_tvar.

  apply_fresh d2ptyping_abs as x; auto.
  apply~ dsubst_mono.
  forwards ~ : H1 x E (F & x ~: A) z.
  rewrite~ concat_assoc.
  rewrite map_push.
  rewrite concat_assoc.
  constructor~.
  apply~ dwft_subst_tvar.
  forwards ~ : H0 x.
  lets [? _]: d2ptyping_regular H2.
  apply* dokt_push_typ_inv.
  rewrite map_push in H2.
  rewrite concat_assoc in H2.
  rewrite~ psubst_te_open_ee_var.

  apply_fresh d2ptyping_gen as x; auto.
  forwards ~ : H0 x E (F & x ~tvar) z.
  rewrite~ concat_assoc.
  rewrite map_push.
  rewrite concat_assoc.
  constructor~.
  rewrite map_push in H1.
  rewrite concat_assoc in H1.
  rewrite~ psubst_te_open_te_var.
  rewrite~ dsubst_tt_open_tt_var.

  apply_fresh d2ptyping_let as x; auto.
  forwards ~ : H0 x E (F & x ~: A) z.
  rewrite~ concat_assoc.
  rewrite map_push.
  rewrite concat_assoc.
  constructor~.
  rewrite map_push in H1.
  rewrite concat_assoc in H1.
  rewrite~ psubst_te_open_ee_var.
Qed.


Lemma d2ptyping_rename_tvar : forall x y E t S f,
  d2ptyping (E & x ~tvar) S (t dopen_tt_var x) (f popen_te_var x) ->
  x \notin dom E \u dfv_tt t \u pfv_te f ->
  y \notin dom E \u dfv_tt t \u pfv_te f ->
  d2ptyping (E & y ~tvar) S (t dopen_tt_var y) (f popen_te_var y)
.
Proof.
  introv Typx Frx Fry.
  tests: (x = y). auto.
  assert  (d2ptyping (E & y ~tvar & map (dsubst_tb x (dtyp_fvar y)) empty) S (dsubst_tt x (dtyp_fvar y) (t dopen_tt_var x)) (psubst_te x (dtyp_fvar y) (f popen_te_var x))).
  apply~ d2ptyping_subst_tvar.
  rewrite~ concat_empty_r.
  rewrite~ map_empty.
  rewrite~ concat_empty_r. constructor~.
  lets [? _]: d2ptyping_regular Typx.
  apply* dokt_push_inv.
  rewrite map_empty in H. clean_empty H.
  rewrite <- dsubst_tt_intro in H; auto.
  rewrite <- psubst_te_intro in H; auto.
Qed.

Lemma d2ptyping'_d2ptyping: forall E e t f,
    d2ptyping' E e t f -> d2ptyping E e t f.
Proof.
  introv ty. inductions ty; autos*.

  apply_fresh d2ptyping_absann as x; auto.
  forwards~ : d2ptyping_rename y IHty; simpls~.
  rewrite <- psubst_ee_intro in H1; auto.

  apply_fresh d2ptyping_abs as x; auto.
  forwards~ : d2ptyping_rename y IHty; simpls~.
  rewrite <- psubst_ee_intro in H1; auto.

  apply_fresh d2ptyping_gen as x; auto.
  forwards~ : d2ptyping_rename_tvar a IHty; simpls~.
  instantiate (TEMP := x). auto.
  auto.

  apply_fresh d2ptyping_let as x; auto.
  forwards~ : d2ptyping_rename y IHty2; simpls~.
  rewrite <- psubst_ee_intro in H0; auto.
Qed.

Hint Constructors d2ptyping'.
Lemma dtyping_d2ptyping': forall E e T,
  dtyping E e T -> exists s, d2ptyping' E e T s.
Proof.
  introv ty. inductions ty; autos*.

  pick_fresh y.
  specializes H1 y.
  destruct H1; auto.
  exists* (ptrm_absann A (pclose_ee y x)).
  apply d2ptyping'_absann with y; auto.
  assert (y \notin pfv_ee (pclose_ee y x)). apply pclose_ee_fresh.
  autos*. rewrite* <- pclose_ee_open.
  lets : d2ptyping'_d2ptyping H1.
  lets : d2ptyping_term H2. auto.

  destruct IHty1.
  destruct IHty2.
  exists~ (ptrm_app (ptrm_cast A (dtyp_arrow A1 A2) x)
               (ptrm_cast A3 A1 x0)).

  pick_fresh y.
  specializes H1 y.
  destruct H1; auto.
  exists* (ptrm_absann A (pclose_ee y x)).
  apply d2ptyping'_abs with y; auto.
  assert (y \notin pfv_ee (pclose_ee y x)). apply pclose_ee_fresh.
  autos*. rewrite* <- pclose_ee_open.
  lets : d2ptyping'_d2ptyping H1.
  lets : d2ptyping_term H2. auto.

  pick_fresh y.
  specializes H0 y.
  destruct H0; auto.
  exists* (ptrm_tabs (pclose_te y x)).
  apply d2ptyping'_gen with y; auto.
  assert (y \notin pfv_te (pclose_te y x)). apply pclose_te_fresh.
  autos*. rewrite* <- pclose_te_open.
  lets : d2ptyping'_d2ptyping H0.
  lets : d2ptyping_term H1. auto.

  pick_fresh y.
  specializes H0 y.
  destruct H0; auto.
  destruct IHty.
  exists* (ptrm_app (ptrm_absann A (pclose_ee y x)) x0) .
  apply d2ptyping'_let with y; auto.
  assert (y \notin pfv_ee (pclose_ee y x)). apply pclose_ee_fresh.
  autos*. rewrite* <- pclose_ee_open.
  lets : d2ptyping'_d2ptyping H0.
  lets : d2ptyping_term H2. auto.
Qed.

Lemma dtyping_d2ptyping: forall E S T,
  dtyping E S T -> exists f, d2ptyping E S T f.
Proof.
  introv ty.
  lets: dtyping_d2ptyping' ty.
  destruct H.
  lets: d2ptyping'_d2ptyping H.
  exists* x.
Qed.

Lemma d2ptyping'_regular : forall E e T f,
  d2ptyping' E e T f -> dokt E /\ dterm e /\ dwft E T /\ pterm f.
Proof.
  introv ty. lets I: d2ptyping'_d2ptyping ty.
  splits~.
  apply* d2ptyping_term.
Qed.

Hint Resolve d2ptyping'_regular.

Hint Extern 1 (dokt ?E) =>
  match goal with
  | H: d2ptyping' _ _ _ _ |- _ => apply (proj41 (d2ptyping'_regular H))
  end.

Hint Extern 1 (dterm ?E) =>
  match goal with
  | H: d2ptyping' _ _ _ _ |- _ => apply (proj42 (d2ptyping'_regular H))
  end.

Hint Extern 1 (dwft ?E ?t) =>
  match goal with
  | H: d2ptyping' _ _ _ _ |- _ => apply (proj43 (d2ptyping'_regular H))
  end.

Hint Extern 1 (pterm ?E ?t) =>
  match goal with
  | H: d2ptyping' _ _ _ _ |- _ => apply (proj44 (d2ptyping'_regular H))
  end.