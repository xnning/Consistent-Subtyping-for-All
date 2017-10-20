Set Implicit Arguments.
Require Import LibLN.
Implicit Types x : var.

Require Import DeclDef DeclInfra DeclProp.

Inductive dtyping' : denv -> dtrm -> dtyp -> Prop :=
  | dtyping'_var : forall E x T,
      dokt E ->
      binds x (dbind_typ T) E ->
      dtyping' E (dtrm_fvar x) T
  | dtyping'_nat : forall E i,
      dokt E ->
      dtyping' E (dtrm_nat i) (dtyp_nat)
  | dtyping'_absann : forall x E A B e,
      dwft empty A ->
      x \notin (dom E \u dfv_ee e \u dfv_tt A \u dfv_tt B) ->
      dtyping' (E & x ~: A) (e dopen_ee_var x) B ->
      dtyping' E (dtrm_absann A e) (dtyp_arrow A B)
  | dtyping'_app : forall E e1 e2 A A1 A2 A3,
      dtyping' E e1 A ->
      dmatch E A A1 A2 ->
      dtyping' E e2 A3 ->
      dconsub E A3 A1 ->
      dtyping' E (dtrm_app e1 e2) A2
  | dtyping'_abs : forall x E A B e,
      x \notin (dom E \u dfv_ee e \u dfv_tt A \u dfv_tt B) ->
      dtyp_mono A ->
      dtyping' (E & x ~: A) (e dopen_ee_var x) B ->
      dtyping' E (dtrm_abs e) (dtyp_arrow A B)
  | dtyping'_gen : forall a E A e,
      a \notin (dom E \u dfv_tt A) ->
      dtyping' (E & a ~tvar) e (A dopen_tt_var a) ->
      dtyping' E e (dtyp_all A)
.

Hint Constructors dtyping dtyping'.
Lemma dtyping_dtyping': forall E e t,
    dtyping E e t -> dtyping' E e t.
Proof.
  induction 1; autos*.
  pick_fresh x.
  apply dtyping'_absann with x; auto.
  pick_fresh x.
  apply dtyping'_abs with x; auto.
  pick_fresh x.
  apply dtyping'_gen with x; auto.
Qed.

Lemma dtyping_subst : forall E F t T z u U,
    dtyping (E & z ~: U & F) t T ->
    dokt (E & u ~: U & F) ->
    dtyping (E & u ~: U & F) (dsubst_ee z (dtrm_fvar u) t) T
.
Proof.
  introv typt. inductions typt; introv okt; simpl; f_equal~.
  case_var*.
    binds_mid~.
    apply dtyping_var; autos*.
    inversions H1.
    apply~ binds_middle_eq.
    lets: dok_from_okt okt.
    lets ~ : ok_middle_inv_r H0.

    apply* dtyping_var.
    forwards ~ : binds_remove H0.
    apply~ binds_weaken.

  apply_fresh dtyping_absann as x; auto.
  specializes H1 x E (F & x ~: A) z U.
  forwards * : H1.
  rewrite* concat_assoc.
  rewrite~ concat_assoc.
  constructor~.
  specializes H0 x. forwards ~ : H0.
  lets~ [? _]: dtyping_regular H2.
  apply dokt_push_typ_inv in H3; auto.
  apply dwft_strengthen_typ in H3.
  apply* dwft_weakening.
  rewrite* dsubst_ee_open_ee_var.
  rewrite concat_assoc in H2; auto.

  apply dtyping_app with (A:=A) (A1:=A1) (A3:=A3); auto.
  apply dmatch_strengthen_typ in H.
  apply* dmatch_weakening.
  apply dconsub_strengthen_typ in H0.
  apply* dconsub_weakening.

  apply_fresh dtyping_abs as x; auto.
  specializes H1 x E (F & x ~: A) z U.
  forwards * : H1.
  rewrite* concat_assoc.
  rewrite~ concat_assoc.
  constructor~.
  specializes H0 x. forwards ~ : H0.
  lets~ [? _]: dtyping_regular H2.
  apply dokt_push_typ_inv in H3; auto.
  apply dwft_strengthen_typ in H3.
  apply* dwft_weakening.
  rewrite* dsubst_ee_open_ee_var.
  rewrite concat_assoc in H2; auto.

  apply_fresh dtyping_gen as x; auto.
  specializes H0 x E (F & x ~tvar) z U.
  forwards * : H0.
  rewrite* concat_assoc.
  rewrite~ concat_assoc.
  rewrite concat_assoc in H1; auto.
Qed.

Lemma dtyping_rename : forall x y E t S V,
  dtyping (E & x ~: V) (S dopen_ee_var x) t ->
  x \notin dom E \u dfv_ee S ->
  y \notin dom E \u dfv_ee S ->
  dtyping (E & y ~: V) (S dopen_ee_var y) t.
Proof.
  introv Typx Frx Fry.
  tests: (x = y). subst*.
  rewrite~ (@dsubst_ee_intro x).
  assert  (dtyping (E & y ~: V & empty) (dsubst_ee x (dtrm_fvar y) (S dopen_ee_var x)) t).
  apply dtyping_subst.
  rewrite~ concat_empty_r.
  rewrite~ concat_empty_r.
  apply~ dokt_typ.
  lets [? [? ?]]: dtyping_regular Typx.
  lets~ : dokt_concat_left_inv H.
  lets [? ?]: dtyping_regular Typx.
  apply* dokt_push_typ_inv.

  rewrite~ concat_empty_r in H.
Qed.

Lemma dtyping_subst_tvar : forall E F t T z u,
    dtyping (E & z ~tvar & F) t T ->
    dokt (E & u ~tvar & map (dsubst_tb z (dtyp_fvar u)) F) ->
    dtyping (E & u ~tvar & map (dsubst_tb z (dtyp_fvar u)) F)
              t (dsubst_tt z (dtyp_fvar u) T).
Proof.
  introv typt. inductions typt; introv okt; simpl; f_equal~.

  apply dtyping_var; autos*.
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
  apply_fresh dtyping_absann as x; auto.
  forwards ~ : H1 x E (F & x ~: A) z.
  rewrite~ concat_assoc.
  rewrite map_push.
  rewrite concat_assoc.
  constructor~.
  apply~ dwft_subst_tvar.
  forwards ~ : H0 x.
  lets [? _]: dtyping_regular H2.
  apply* dokt_push_typ_inv.
  rewrite map_push in H2.
  rewrite concat_assoc in H2; auto.
  simpl in H2. rewrite I in H2; auto.

  apply dtyping_app with (A:= (dsubst_tt z (dtyp_fvar u) A))
                         (A1:= (dsubst_tt z (dtyp_fvar u) A1))
                         (A3 := (dsubst_tt z (dtyp_fvar u) A3)); auto.
  apply~ dmatch_subst_tvar.
  apply~ dconsub_subst_tvar.

  apply_fresh dtyping_abs as x; auto.
  apply~ dsubst_mono.
  forwards ~ : H1 x E (F & x ~: A) z.
  rewrite~ concat_assoc.
  rewrite map_push.
  rewrite concat_assoc.
  constructor~.
  apply~ dwft_subst_tvar.
  forwards ~ : H0 x.
  lets [? _]: dtyping_regular H2.
  apply* dokt_push_typ_inv.
  rewrite map_push in H2.
  rewrite concat_assoc in H2; auto.

  apply_fresh dtyping_gen as x; auto.
  forwards ~ : H0 x E (F & x ~tvar) z.
  rewrite~ concat_assoc.
  rewrite map_push.
  rewrite concat_assoc.
  constructor~.
  rewrite map_push in H1.
  rewrite concat_assoc in H1.
  rewrite~ dsubst_tt_open_tt_var.
Qed.

Lemma dtyping_rename_tvar : forall x y E t S,
  dtyping (E & x ~tvar) S (t dopen_tt_var x)  ->
  x \notin dom E \u dfv_tt t ->
  y \notin dom E \u dfv_tt t ->
  dtyping (E & y ~tvar) S (t dopen_tt_var y)
.
Proof.
  introv Typx Frx Fry.
  tests: (x = y). auto.
  assert  (dtyping (E & y ~tvar & map (dsubst_tb x (dtyp_fvar y)) empty) S (dsubst_tt x (dtyp_fvar y) (t dopen_tt_var x))).
  apply~ dtyping_subst_tvar.
  rewrite~ concat_empty_r.
  rewrite~ map_empty.
  rewrite~ concat_empty_r. constructor~.
  lets [? _]: dtyping_regular Typx.
  apply* dokt_push_inv.
  rewrite map_empty in H. clean_empty H.
  rewrite <- dsubst_tt_intro in H; auto.
Qed.

Lemma dtyping'_dtyping: forall E e t,
    dtyping' E e t -> dtyping E e t.
Proof.
  introv ty. inductions ty; autos~.

  apply_fresh dtyping_absann as x; auto.
  forwards~ : dtyping_rename y IHty; simpls~.

  apply* dtyping_app.

  apply_fresh dtyping_abs as x; auto.
  forwards~ : dtyping_rename y IHty; simpls~.

  apply_fresh dtyping_gen as x; auto.
  forwards~ : dtyping_rename_tvar a IHty; simpls~; auto.
  instantiate (TEMP := x); auto.
  auto.
Qed.
