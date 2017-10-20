Set Implicit Arguments.

Require Import LibLN.
Implicit Types x : var.
Require Import DeclDef DeclInfra.

(** Subtyping *)

Inductive dsub' : denv -> dtyp -> dtyp -> Prop :=
  | dsub'_nat : forall E,
      dokt E ->
      dsub' E dtyp_nat dtyp_nat
  | dsub'_var : forall E x,
      dokt E ->
      binds x dbind_tvar E ->
      dsub' E (dtyp_fvar x) (dtyp_fvar x)
  | dsub'_unknown : forall E,
      dokt E ->
      dsub' E dtyp_unknown dtyp_unknown
  | dsub'_fun : forall E A1 A2 B1 B2,
      dsub' E B1 A1 ->
      dsub' E A2 B2 ->
      dsub' E (dtyp_arrow A1 A2) (dtyp_arrow B1 B2)
  | dsub'_allL : forall E A B tau,
      dtyp_mono tau ->
      dwft E tau ->
      dsub' E (dopen_tt A tau) B ->
      dsub' E (dtyp_all A) B
  | dsub'_allR : forall x E A B,
      x \notin dom E \u dfv_tt_env E \u dfv_tt A \u dfv_tt B ->

      dsub' (E & x ~tvar) A (B dopen_tt_var x) ->
      dsub' E A (dtyp_all B)
.

Hint Constructors dsub dsub'.

Lemma dsub_dsub': forall E A B,
    dsub E A B -> dsub' E A B.
Proof.
  induction 1; autos*.
  pick_fresh x.
  apply dsub'_allR with x; auto.
Qed.

Lemma dsub_subst : forall F E A B z u,
    dsub (E & z ~tvar & F) A B ->
    dokt (E & u ~tvar & F) ->
    dsub (E & u ~tvar & F) (dsubst_tt z (dtyp_fvar u) A)
                           (dsubst_tt z (dtyp_fvar u) B)
.
Proof.
  introv typt. inductions typt; introv okt; simpl; f_equal~.
  case_var*.
    binds_mid~.
    apply dsub_var; autos*.
    apply~ binds_middle_eq.
    lets: dok_from_okt okt.
    lets ~ : ok_middle_inv_r H0.

    apply* dsub_var.
    forwards ~ : binds_remove H0.
    apply~ binds_weaken.

  forwards ~ : IHtypt F E z.
  apply dsub_allL with (dsubst_tt z (dtyp_fvar u) tau); auto.
  apply~ dsubst_mono.
  apply~ dwft_rename.
  rewrite~ <- dsubst_tt_open_tt.

  apply_fresh dsub_allR as x.
  forwards ~ : H0 x (F & x ~tvar) E z.
  rewrite~ concat_assoc.
  rewrite~ concat_assoc.
  rewrite concat_assoc in H1.
  rewrite~ dsubst_tt_open_tt_var.
Qed.

Lemma dsub_rename : forall E x y A B,
  dsub (E & x ~tvar) (A dopen_tt_var x) (B dopen_tt_var x) ->
  x \notin dom E \u dfv_tt A \u dfv_tt B ->
  y \notin dom E \u dfv_tt A \u dfv_tt B ->
  dsub (E & y ~tvar) (A dopen_tt_var y) (B dopen_tt_var y)
.
Proof.
  introv Typx Frx Fry.
  tests: (x = y). subst*.
  rewrite~ (@dsubst_tt_intro x).
  pattern (B dopen_tt_var y) at 1; rewrite~ (@dsubst_tt_intro x).
  apply_empty~ dsub_subst.
  apply~ dokt_tvar.
  lets [? ?]: dsub_regular Typx.
  lets~ : dokt_concat_left_inv H.
Qed.

Lemma dsub'_dsub: forall E A B,
    dsub' E A B -> dsub E A B.
Proof.
  introv ty. inductions ty; autos~.

  apply dsub_allL with tau; auto.

  apply_fresh dsub_allR as x; auto.
  assert (A dopen_tt_var x = A). unfold dopen_tt. rewrite~ <- dopen_tt_rec_type.
  forwards ~ [? [? ?]] : dsub_regular IHty.
  assert (A dopen_tt_var y = A). unfold dopen_tt. rewrite~ <- dopen_tt_rec_type.
  forwards ~ [? [? ?]] : dsub_regular IHty.
  rewrite <- H0 in IHty.
  forwards* : dsub_rename y IHty; simpls~.
  rewrite H1 in H2; auto.
Qed.

Lemma dsub'_refl: forall E t,
    dokt E ->
    dwft E t ->
    dsub' E t t.
Proof.
  introv ok wf.
  induction wf; simpls~.
  pick_fresh x.
  apply dsub'_allR with x; auto. simpls~.
  apply dsub'_allL with (dtyp_fvar x); auto.
Qed.
Hint Resolve dsub'_refl.

Lemma dsub'_regular: forall E A B,
    dsub' E A B -> dokt E /\ dwft E A /\ dwft E B.
Proof.
  introv sub.
  apply dsub'_dsub in sub; auto.
Qed.

Hint Extern 1 (dokt ?E) =>
  match goal with
  | H: dsub' _ _ _ |- _ => apply (proj31 (dsub'_regular H))
  end.

Hint Extern 1 (dwft ?E ?t) =>
  match goal with
  | H: dsub' _ _ _ |- _ => apply (proj32 (dsub'_regular H))
  | H: dsub' _ _ _ |- _ => apply (proj33 (dsub'_regular H))
  end.

(** DSUB SIZE *)

Inductive dsub_size : denv -> dtyp -> dtyp -> nat -> Prop :=
  |dsub_size_nat : forall E,
     dokt E ->
     dsub_size E dtyp_nat dtyp_nat 1
  |dsub_size_var : forall E x,
      dokt E ->
      binds x dbind_tvar E ->
     dsub_size E (dtyp_fvar x) (dtyp_fvar x) 1
  |dsub_size_unknown : forall E,
      dokt E ->
      dsub_size E dtyp_unknown dtyp_unknown 1
  |dsub_size_arrow : forall E A1 A2 B1 B2 n1 n2,
     dsub_size E B1 A1 n1 ->
     dsub_size E A2 B2 n2 ->
     dsub_size E (dtyp_arrow A1 A2) (dtyp_arrow B1 B2) (1 + n1 + n2)
  |dsub_size_allL : forall E A2 B2 tau n1,
     dtyp_mono tau ->
     dwft E tau ->
     dsub_size E (dopen_tt A2 tau) B2 n1 ->
     dsub_size E (dtyp_all A2) B2 (1 + n1)
  |dsub_size_allR : forall L E A2 B2 n1,
     (forall x, x \notin L ->
           dsub_size (E & x ~tvar) A2 (B2 dopen_tt_var x) n1) ->
     dsub_size E A2 (dtyp_all B2) (1 + n1)
.

Hint Constructors dsub_size.

Lemma dsub_size_dsub: forall E t1 t2 n,
    dsub_size E t1 t2 n ->
    dsub E t1 t2.
Proof.
  introv sub. induction sub; autos~.
  apply dsub_allL with tau; auto.
  apply_fresh dsub_allR as x; auto.
Qed.

Lemma dsub_size_subst : forall F E A B z u n,
    dsub_size (E & z ~tvar & F) A B n ->
    dokt (E & u ~tvar & F) ->
    dsub_size (E & u ~tvar & F) (dsubst_tt z (dtyp_fvar u) A)
                                (dsubst_tt z (dtyp_fvar u) B) n
.
Proof.
  introv typt. inductions typt; introv okt; simpl; f_equal~.
  case_var*.
    binds_mid~.
    apply dsub_size_var; autos*.
    apply~ binds_middle_eq.
    lets: dok_from_okt okt.
    lets ~ : ok_middle_inv_r H0.

    apply* dsub_size_var.
    forwards ~ : binds_remove H0.
    apply~ binds_weaken.

  forwards ~ : IHtypt1 F E z.
  forwards ~ : IHtypt2 F E z.
  apply~ dsub_size_arrow.

  forwards ~ : IHtypt F E z.
  apply dsub_size_allL with (dsubst_tt z (dtyp_fvar u) tau); auto.
  apply~ dsubst_mono.
  apply~ dwft_rename.
  rewrite~ <- dsubst_tt_open_tt.

  apply_fresh dsub_size_allR as x.
  forwards ~ : H0 x (F & x ~tvar) E z.
  rewrite~ concat_assoc.
  rewrite~ concat_assoc.
  rewrite concat_assoc in H1.
  rewrite~ dsubst_tt_open_tt_var.
Qed.

Lemma dsub_size_regular : forall E A B n,
  dsub_size E A B n -> dokt E /\ dwft E A /\ dwft E B.
Proof.
  introv sub.
  forwards ~ : dsub_size_dsub sub.
Qed.

Hint Extern 1 (dokt ?E) =>
  match goal with
  | H: dsub_size _ _ _ |- _ => apply (proj31 (dsub_size_regular H))
  end
.

Hint Extern 1 (dwft ?E ?t) =>
  match goal with
  | H: dsub_size _ _ _ |- _ => apply (proj32 (dsub_size_regular H))
  | H: dsub_size _ _ _ |- _ => apply (proj33 (dsub_size_regular H))
  end
.

Lemma dsub_size_rename : forall E x y A B n,
  dsub_size (E & x ~tvar) (A dopen_tt_var x) (B dopen_tt_var x) n ->
  x \notin dom E \u dfv_tt A \u dfv_tt B ->
  y \notin dom E \u dfv_tt A \u dfv_tt B ->
  dsub_size (E & y ~tvar) (A dopen_tt_var y) (B dopen_tt_var y) n
.
Proof.
  introv Typx Frx Fry.
  tests: (x = y). subst*.
  rewrite~ (@dsubst_tt_intro x).
  pattern (B dopen_tt_var y) at 1; rewrite~ (@dsubst_tt_intro x).
  apply_empty~ dsub_size_subst.
  apply~ dokt_tvar.
  lets [? ?]: dsub_size_regular Typx.
  lets~ : dokt_concat_left_inv H.
Qed.

Lemma dsub_dsub_size: forall E t1 t2,
    dsub E t1 t2 ->
    exists n, dsub_size E t1 t2 n.
Proof.
  introv sub. induction sub; autos~; try(solve[exists~ 1]).
  destruct IHsub1 as (n1 & ?).
  destruct IHsub2 as (n2 & ?).
  exists~ (1 + n1 + n2).

  destruct IHsub as (n1 & ?).
  exists~ (1 + n1).
  apply dsub_size_allL with tau; auto.

  pick_fresh y. forwards ~ : H0 y.
  destruct H1 as (n1 & ?).
  exists~ (1 + n1).
  apply_fresh dsub_size_allR as z; auto.
  assert (A dopen_tt_var y = A). unfold dopen_tt. rewrite~ <- dopen_tt_rec_type.
  forwards ~ [? [? ?]] : dsub_size_regular H1.
  assert (A dopen_tt_var z = A). unfold dopen_tt. rewrite~ <- dopen_tt_rec_type.
  forwards ~ [? [? ?]] : dsub_size_regular H1.
  rewrite <- H2 in H1.
  rewrite <- H3.
  apply* dsub_size_rename.
Qed.

Hint Constructors dconsub.
Lemma dsub_size_consub: forall E A B n,
    dsub_size E A B n ->
    dconsub E A B.
Proof.
  introv sub. inductions sub; auto.
  apply dconsub_allL with tau; auto.
  apply_fresh dconsub_allR as x; auto.
Qed.
Hint Resolve dsub_size_consub.

Lemma dsub_size_weakening : forall F E x v A B n,
    dsub_size (E & F) A B n ->
    dokt (E & x ~ v & F) ->
    dsub_size (E & x ~ v & F) A B n.
Proof.
  introv sub. gen v.
  inductions sub; introv okt; simpls~.
  apply~ dsub_size_var.
  apply~ binds_weaken.

  apply~ dsub_size_arrow.

  apply dsub_size_allL with tau; auto.

  apply_fresh dsub_size_allR as x; auto.
  rewrite <- concat_assoc.
  apply~ H0.
  rewrite~ concat_assoc.
  rewrite~ concat_assoc.
Qed.

Lemma dsub_size_push : forall E x v A B n,
    dsub_size E A B n ->
    dokt (E & x ~ v) ->
    dsub_size (E & x ~ v) A B n.
Proof.
  intros.
  apply_empty~ dsub_size_weakening.
Qed.
