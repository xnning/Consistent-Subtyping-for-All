Require Import TLC.LibLN.
Require Import DeclDef DeclInfra DeclProp.

(** * OL TYPE SYSTEM *)

Inductive otyping : denv -> dtrm -> dtyp -> Prop :=
  | otyping_var : forall E x T,
      denv_static E ->
      binds x (dbind_typ T) E ->
      otyping E (dtrm_fvar x) T
  | otyping_nat : forall E i,
      denv_static E ->
      otyping E (dtrm_nat i) (dtyp_nat)
  | otyping_absann : forall L E A B e,
      dwft empty A ->
      (forall x, x \notin L ->
            otyping (E & x ~: A) (e dopen_ee_var x) B) ->
      otyping E (dtrm_absann A e) (dtyp_arrow A B)
  | otyping_abs : forall L E A B e,
      dtyp_mono A ->
      (forall x, x \notin L ->
            otyping (E & x ~: A) (e dopen_ee_var x) B) ->
      otyping E (dtrm_abs e) (dtyp_arrow A B)
  | otyping_app : forall E e1 e2 A1 A2,
      otyping E e1 (dtyp_arrow A1 A2) ->
      otyping E e2 A1 ->
      otyping E (dtrm_app e1 e2) A2
  | otyping_sub : forall E e A B,
      otyping E e A ->
      dsub E A B ->
      otyping E e B
  | otyping_gen : forall L E A e,
      (forall a, a \notin L ->
            otyping (E & a ~tvar) e (A dopen_tt_var a)) ->
      otyping E e (dtyp_all A)
  | otyping_let : forall L E e1 e2 A B,
      otyping E e1 A ->
      (forall x, x \notin L ->
            otyping (E & x ~: A) (e2 dopen_ee_var x) B) ->
      otyping E (dtrm_let e1 e2) B
.

Lemma otyping_regular : forall E e T,
    otyping E e T ->
    denv_static E /\ dterm_static e /\ dtyp_static T /\ dwft E T.
Proof.
  induction 1; try(solve[auto;splits~]).
  splits~. apply* denv_static_dtyp.
  apply* dwft_from_env_has_typ.
  apply* denv_static_dokt.

  splits~.
  forwards ~ : denv_static_dokt H.

  assert (sa: dtyp_static A).
  pick_fresh y. specializes H1 y. destructs~ H1.
  apply* denv_static_push_inv_dtyp.
  splits~.
    pick_fresh y. specializes H1 y. destructs~ H1.
      apply* denv_static_push_inv.
    apply_fresh dterm_static_absann as y; auto.
      specializes H1 y. destructs~ H1.
    apply~ dtyp_static_arrow.
      pick_fresh y. specializes H1 y. destructs~ H1.
    pick_fresh y. specializes H1 y. destructs~ H1.
      apply denv_static_dokt in H1.
      constructor~.
      apply* dokt_push_typ_inv.
      apply* dwft_strengthen_push.

  assert (sa: dtyp_static A).
    apply~ dtyp_mono_static.
  splits~.
    pick_fresh y. specializes H1 y. destructs~ H1.
      apply* denv_static_push_inv.
    apply_fresh dterm_static_abs as y; auto.
      specializes H1 y. destructs~ H1.
    apply~ dtyp_static_arrow.
      pick_fresh y. specializes H1 y. destructs~ H1.
    pick_fresh y. specializes H1 y. destructs~ H1.
      apply denv_static_dokt in H1.
      constructor~.
      apply* dokt_push_typ_inv.
      apply* dwft_strengthen_push.

  destruct IHotyping1 as [? [? [? ?]]].
  destruct IHotyping2 as [? [? [? ?]]]. splits~.
  inversions~ H3.
  inversions~ H4.

  destruct IHotyping as [? [? [? ?]]].
  splits~.
  apply dsub_static_l with E A; auto.

  splits~.
    pick_fresh y. specializes H0 y. destructs~ H0.
      apply* denv_static_push_inv.
    pick_fresh y. specializes H0 y. destructs~ H0.
    apply_fresh dtyp_static_all as y.
      specializes H0 y. destructs~ H0.
    apply_fresh dwft_all as y.
      specializes H0 y. destructs~ H0.

  destructs IHotyping. splits~.
    apply_fresh dterm_static_let as y; auto.
      specializes H1 y. destructs~ H1.
    pick_fresh y. specializes H1 y. destructs~ H1.
    pick_fresh y. specializes H1 y. destructs~ H1.
    apply* dwft_strengthen_push.
Qed.
