Set Implicit Arguments.

From TLC Require Import LibLN.

Require Import DeclDef.


(** Computing free term variables in a term *)

Fixpoint dfv_ee (e : dtrm) {struct e} : vars :=
  match e with
  | dtrm_bvar i       => \{}
  | dtrm_fvar x       => \{x}
  | dtrm_nat i        => \{}
  | dtrm_absann V e1  => (dfv_ee e1)
  | dtrm_abs e1       => (dfv_ee e1)
  | dtrm_app e1 e2    => (dfv_ee e1) \u (dfv_ee e2)
  | dtrm_let e1 e2    => (dfv_ee e1) \u (dfv_ee e2)
  end.

(** Substitution for free term variables in terms. *)

Fixpoint dsubst_ee (z : var) (u : dtrm) (e : dtrm) {struct e} : dtrm :=
  match e with
  | dtrm_bvar i       => dtrm_bvar i
  | dtrm_fvar x       => If x = z then u else (dtrm_fvar x)
  | dtrm_nat i        => dtrm_nat i
  | dtrm_absann V e1  => dtrm_absann V (dsubst_ee z u e1)
  | dtrm_abs e1       => dtrm_abs (dsubst_ee z u e1)
  | dtrm_app e1 e2    => dtrm_app (dsubst_ee z u e1) (dsubst_ee z u e2)
  | dtrm_let e1 e2    => dtrm_let (dsubst_ee z u e1) (dsubst_ee z u e2)
  end.

(** Computing free type variables in a type *)

Fixpoint dfv_tt (T : dtyp) {struct T} : vars :=
  match T with
  | dtyp_nat         => \{}
  | dtyp_unknown     => \{}
  | dtyp_bvar J      => \{}
  | dtyp_fvar X      => \{X}
  | dtyp_arrow T1 T2 => (dfv_tt T1) \u (dfv_tt T2)
  | dtyp_all T1      => (dfv_tt T1)
  end.

(** Substitution for free type variables in types. *)

Fixpoint dsubst_tt (Z : var) (U : dtyp) (T : dtyp) {struct T} : dtyp :=
  match T with
  | dtyp_nat         => dtyp_nat
  | dtyp_unknown     => dtyp_unknown
  | dtyp_bvar J      => dtyp_bvar J
  | dtyp_fvar X      => If X = Z then U else (dtyp_fvar X)
  | dtyp_arrow T1 T2 => dtyp_arrow (dsubst_tt Z U T1) (dsubst_tt Z U T2)
  | dtyp_all T1      => dtyp_all (dsubst_tt Z U T1)
  end.

(** Substitution for free type variables in environment. *)

Definition dsubst_tb (Z : var) (P : dtyp) (b : dbind) : dbind :=
  match b with
  | dbind_tvar => dbind_tvar
  | dbind_typ T => dbind_typ (dsubst_tt Z P T)
  end.

(** Computing free type variables in a env *)

Fixpoint dfv_tt_env (E : denv) {struct E} : vars :=
  match E with
  | nil                      => \{}
  | cons (x, dbind_typ t) E' => dfv_tt t \u dfv_tt_env E'
  | cons (x, dbind_tvar) E'  => dfv_tt_env E'
  end.

(** * Tactics *)

(** Constructors as hints. *)

Hint Constructors dtype dterm dokt dokt dtyp_mono.

Ltac gather_vars :=
  let A := gather_vars_with (fun x : vars => x) in
  let B := gather_vars_with (fun x : var => \{x}) in
  let C := gather_vars_with (fun x : dtrm => dfv_ee x) in
  let D := gather_vars_with (fun x : dtyp => dfv_tt x) in
  let E := gather_vars_with (fun x : denv => dom x) in
  let F := gather_vars_with (fun x : denv => dfv_tt_env x) in
  constr:(A \u B \u C \u D \u E \u F).

(** "pick_fresh x" tactic create a fresh variable with name x *)

Ltac pick_fresh X :=
  let L := gather_vars in (pick_fresh_gen L X).

(** "apply_fresh T as x" is used to apply inductive rule which
   use an universal quantification over a cofinite set *)

Tactic Notation "apply_fresh" constr(T) "as" ident(x) :=
  apply_fresh_base T gather_vars x.

Tactic Notation "apply_fresh" "*" constr(T) "as" ident(x) :=
  apply_fresh T as x; autos*.

(* ********************************************************************** *)
(** ** Properties of type substitution in type *)

(** Substitution on indices is identity on well-formed terms. *)

Lemma dopen_tt_rec_type_core : forall T j V U i, i <> j ->
  (dopen_tt_rec j V T) = dopen_tt_rec i U (dopen_tt_rec j V T) ->
  T = dopen_tt_rec i U T.
Proof.
  induction T; introv Neq H; simpl in *; inversion H; f_equal*.
  case_nat*. case_nat*.
Qed.

Lemma dopen_tt_rec_type : forall T U,
  dtype T -> forall k, T = dopen_tt_rec k U T.
Proof.
  induction 1; intros; simpl; f_equal*.
  pick_fresh X. apply* (@dopen_tt_rec_type_core T2 0 (dtyp_fvar X)).
Qed.

(** Substitution for a fresh name is identity. *)

Lemma dsubst_tt_fresh : forall Z U T,
  Z \notin dfv_tt T -> dsubst_tt Z U T = T.
Proof.
  induction T; simpl; intros; f_equal*.
  case_var*.
Qed.

(** Substitution distributes on the open operation. *)

Lemma dsubst_tt_open_tt_rec : forall T1 T2 X P n, dtype P ->
  dsubst_tt X P (dopen_tt_rec n T2 T1) =
  dopen_tt_rec n (dsubst_tt X P T2) (dsubst_tt X P T1).
Proof.
  introv WP. generalize n.
  induction T1; intros k; simpls; f_equal*.
  case_nat*.
  case_var*. rewrite* <- dopen_tt_rec_type.
Qed.

Lemma dsubst_tt_open_tt : forall T1 T2 X P, dtype P ->
  dsubst_tt X P (dopen_tt T1 T2) =
  dopen_tt (dsubst_tt X P T1) (dsubst_tt X P T2).
Proof.
  unfold dopen_tt. autos* dsubst_tt_open_tt_rec.
Qed.

(** Substitution and open_var for distinct names commute. *)

Lemma dsubst_tt_open_tt_var : forall X Y U T, Y <> X -> dtype U ->
  (dsubst_tt X U T) dopen_tt_var Y = dsubst_tt X U (T dopen_tt_var Y).
Proof.
  introv Neq Wu. rewrite* dsubst_tt_open_tt.
  simpl. case_var*.
Qed.

(** Opening up a body t with a type u is the same as opening
  up the abstraction with a fresh name x and then substituting u for x. *)

Lemma dsubst_tt_intro : forall X T2 U,
  X \notin dfv_tt T2 -> dtype U ->
  dopen_tt T2 U = dsubst_tt X U (T2 dopen_tt_var X).
Proof.
  introv Fr Wu. rewrite* dsubst_tt_open_tt.
  rewrite* dsubst_tt_fresh. simpl. case_var*.
Qed.

Lemma dsubst_tt_rec_intro : forall X T2 U k,
  X \notin dfv_tt T2 -> dtype U ->
  dopen_tt_rec k U T2 = dsubst_tt X U (dopen_tt_rec k (dtyp_fvar X) T2).
Proof.
  introv Fr Wu. rewrite* dsubst_tt_open_tt_rec.
  simpls. case_var~.
  rewrite* dsubst_tt_fresh.
Qed.

Lemma dopen_tt_rec_type_commu : forall e j v u i, i <> j ->
  dtype v -> dtype u ->
  dopen_tt_rec j v (dopen_tt_rec i u e) = dopen_tt_rec i u (dopen_tt_rec j v e).
Proof.
  induction e; introv Neq tv tu; simpl in *; auto.
  f_equal*.
  case_nat*. case_nat*. simpls. case_nat*.
  symmetry. apply~ dopen_tt_rec_type.
  case_nat*.
  simpls. case_nat*.
  apply~ dopen_tt_rec_type.
  simpls. case_nat*. case_nat*.
  f_equal*.
Qed.

(** substitute a mono type with a mono type gives back mono type **)

Lemma dsubst_mono: forall U u z,
    dtyp_mono U ->
    dtyp_mono u ->
    dtyp_mono (dsubst_tt z u U).
Proof.
  introv mu me. inductions mu; simpls; auto.
  case_var*.
Qed.

Lemma dtyp_mono_dtype: forall A,
    dtyp_mono A ->
    dtype A.
Proof.
  introv mn. inductions mn; auto.
Qed.


(** Substitutions preserve local closure. *)

Lemma dsubst_tt_type : forall T Z P,
  dtype T -> dtype P -> dtype (dsubst_tt Z P T).
Proof.
  induction 1; intros; simpl; auto.
  case_var*.
  apply_fresh* dtype_all as X. rewrite* dsubst_tt_open_tt_var.
Qed.

(* ********************************************************************** *)
(** ** Properties of term substitution in terms *)

Lemma dopen_ee_rec_term_core : forall e j v u i, i <> j ->
  dopen_ee_rec j v e = dopen_ee_rec i u (dopen_ee_rec j v e) ->
  e = dopen_ee_rec i u e.
Proof.
  induction e; introv Neq H; simpl in *; inversion H; f_equal*.
  case_nat*. case_nat*.
Qed.

Lemma dopen_ee_rec_term : forall u e,
  dterm e -> forall k, e = dopen_ee_rec k u e.
Proof.
  induction 1; intros; simpl; f_equal*.
  unfolds dopen_ee. pick_fresh x.
   apply* (@dopen_ee_rec_term_core e1 0 (dtrm_fvar x)).
  unfolds dopen_ee. pick_fresh x.
   apply* (@dopen_ee_rec_term_core e1 0 (dtrm_fvar x)).
  unfolds dopen_ee. pick_fresh x.
   apply* (@dopen_ee_rec_term_core e2 0 (dtrm_fvar x)).
Qed.

(** Substitution for a fresh name is identity. *)

Lemma dsubst_ee_fresh : forall x u e,
  x \notin dfv_ee e -> dsubst_ee x u e = e.
Proof.
  induction e; simpl; intros; f_equal*.
  case_var*.
Qed.

(** Substitution distributes on the open operation. *)

Lemma dsubst_ee_open_ee : forall t1 t2 u x, dterm u ->
  dsubst_ee x u (dopen_ee t1 t2) =
  dopen_ee (dsubst_ee x u t1) (dsubst_ee x u t2).
Proof.
  intros. unfold dopen_ee. generalize 0.
  induction t1; intros; simpls; f_equal*.
  case_nat*.
  case_var*. rewrite* <- dopen_ee_rec_term.
Qed.

(** Substitution and open_var for distinct names commute. *)

Lemma dsubst_ee_open_ee_var : forall x y u e, y <> x -> dterm u ->
  (dsubst_ee x u e) dopen_ee_var y = dsubst_ee x u (e dopen_ee_var y).
Proof.
  introv Neq Wu. rewrite* dsubst_ee_open_ee.
  simpl. case_var*.
Qed.

(** Opening up a body t with a type u is the same as opening
  up the abstraction with a fresh name x and then substituting u for x. *)

Lemma dsubst_ee_intro : forall x u e,
  x \notin dfv_ee e -> dterm u ->
  dopen_ee e u = dsubst_ee x u (e dopen_ee_var x).
Proof.
  introv Fr Wu. rewrite* dsubst_ee_open_ee.
  rewrite* dsubst_ee_fresh. simpl. case_var*.
Qed.

(** Substitutions preserve local closure. *)

Lemma dsubst_ee_term : forall e1 Z e2,
  dterm e1 -> dterm e2 -> dterm (dsubst_ee Z e2 e1).
Proof.
  induction 1; intros; simpl; auto.
  case_var*.
  apply_fresh* dterm_absann as y. rewrite* dsubst_ee_open_ee_var.
  apply_fresh* dterm_abs as y. rewrite* dsubst_ee_open_ee_var.
  apply_fresh* dterm_let as y. rewrite* dsubst_ee_open_ee_var.
Qed.

Lemma dterm_subst : forall t z u,
    dterm t ->
    dterm (dsubst_ee z (dtrm_fvar u) t)
.
Proof.
  introv typt.
  apply* dsubst_ee_term.
Qed.

Lemma dterm_rename : forall x y S,
  dterm (S dopen_ee_var x) ->
  x \notin dfv_ee S ->
  y \notin dfv_ee S ->
  dterm (S dopen_ee_var y).
Proof.
  introv Typx Frx Fry.
  tests: (x = y). subst*.
  rewrite~ (@dsubst_ee_intro x).
  apply~ dterm_subst.
Qed.

Hint Resolve dsubst_tt_type dsubst_ee_term.

(** Open_var with fresh names is an injective operation *)

Lemma dopen_ee_rec_inj : forall x t1 t2 k,
  x \notin (dfv_ee t1) -> x \notin (dfv_ee t2) ->
  (dopen_ee_rec k (dtrm_fvar x) t1 = dopen_ee_rec k (dtrm_fvar x) t2) -> (t1 = t2).
Proof.
  intros x t1.
  induction t1; intros t2 k; destruct t2; simpl; intros; inversion H1;
  try solve [ f_equal*
  | do 2 try case_nat; inversions* H1; try notin_false ].
Qed.

Lemma dopen_tt_rec_inj : forall x t1 t2 k,
  x \notin (dfv_tt t1) -> x \notin (dfv_tt t2) ->
  (dopen_tt_rec k (dtyp_fvar x) t1 = dopen_tt_rec k (dtyp_fvar x) t2) -> (t1 = t2).
Proof.
  intros x t1.
  induction t1; intros t2 k; destruct t2; simpl; intros; inversion H1;
  try solve [ f_equal*
  | do 2 try case_nat; inversions* H1; try notin_false ].
Qed.

Hint Resolve dopen_ee_rec_inj dopen_tt_rec_inj.

(** More properties about free variables *)

Lemma notin_subst: forall x A B,
    x \notin dfv_tt A ->
    x \notin dfv_tt (dsubst_tt x A B).
Proof.
  introv neq. inductions B; simpls~.
  case_var~.
  simpls~.
Qed.

Lemma dnotin_fv_tt_subst_inv: forall V z x U,
    z \notin dfv_tt U ->
    z \notin dfv_tt V ->
    z <> x ->
    z \notin dfv_tt (dsubst_tt x U V).
Proof.
  induction V; introv notinu notinv neq; simpls~.
  case_var~.
Qed.

Hint Resolve dnotin_fv_tt_subst_inv.

(* ********************************************************************** *)
(** ** Free Variables *)

Lemma din_open_tt_rec: forall x T k U,
    x \in dfv_tt T ->
    x \in dfv_tt (dopen_tt_rec k U T).
Proof.
  intros. gen x k U. induction T; simpls~; intros.
  rewrite in_union in *.
  destruct H.
  left. apply* IHT1.
  right. apply* IHT2.
  case_nat~.
  rewrite in_empty in H. false~.
Qed.

Lemma din_open_tt_var: forall x T y,
    x \in dfv_tt T ->
    x \in dfv_tt (T dopen_tt_var y).
Proof.
  intros. unfolds dopen_tt. apply* din_open_tt_rec.
Qed.

Lemma dnotin_fv_tt_open : forall Y X T,
  X \notin dfv_tt (T dopen_tt_var Y) ->
  X \notin dfv_tt T.
Proof.
 introv. unfold dopen_tt. generalize 0.
 induction T; simpl; intros k Fr; auto.
 specializes IHT1 k. specializes IHT2 k. auto.
 specializes IHT (S k). auto.
Qed.

Lemma dnotin_fv_tt_dopen : forall Y X T,
  X \notin dfv_tt (dopen_tt T Y) ->
  X \notin dfv_tt T.
Proof.
 introv. unfold dopen_tt. generalize 0.
 induction T; simpl; intros k Fr; auto.
 specializes IHT1 k. specializes IHT2 k. auto.
 specializes IHT (S k). auto.
Qed.

Lemma dnotin_fv_tt_open_inv : forall X T U k,
  X \notin dfv_tt T ->
  X \notin dfv_tt U ->
  X \notin dfv_tt (dopen_tt_rec k U T).
Proof.
  introv notint notinu. gen k.
  inductions T; introv; simpls~.
  case_nat*.
Qed.

Lemma  dfv_tt_env_push_typ_inv: forall G x v,
  dfv_tt_env (G & x ~: v) = dfv_tt v \u dfv_tt_env G.
Proof.
  introv.
  rewrite <- cons_to_push.
  simpls~.
Qed.

Lemma  dfv_tt_env_push_tvar_inv: forall G x,
  dfv_tt_env (G & x ~tvar) = dfv_tt_env G.
Proof.
  introv.
  rewrite <- cons_to_push.
  simpls~.
Qed.

Lemma dnotin_fv_tt_env_bind_inv: forall E x T y,
    binds y (dbind_typ T) E ->
    x \notin dfv_tt_env E ->
    x \notin dfv_tt T.
Proof.
  induction E using env_ind; introv bd hy.
  false* binds_empty_inv.
  apply binds_push_inv in bd.
  destruct bd as [[v1 v2]| [v3 v4]].
  subst. rewrite dfv_tt_env_push_typ_inv in hy. autos*.
  apply* IHE.
  destruct v.
  rewrite dfv_tt_env_push_tvar_inv in hy; auto.
  rewrite dfv_tt_env_push_typ_inv in hy; auto.
Qed.


(* ********************************************************************** *)
(** * Relations between well-formed environment and types well-formed
  in environments *)

Lemma dtype_open : forall U T2,
  dtype (dtyp_all T2) ->
  dtype U ->
  dtype (dopen_tt T2 U).
Proof.
  introv WA WU. inversions WA. pick_fresh X.
  rewrite* (@dsubst_tt_intro X).
Qed.

(** If an environment is well-formed, then it does not contain duplicated keys. *)

Lemma dok_from_okt : forall E,
  dokt E -> ok E.
Proof.
  induction 1; auto.
Qed.

Hint Extern 1 (ok _) => apply dok_from_okt.

Lemma dokt_push_inv : forall E x T,
  dokt (E & x ~ T) -> dokt E /\  x # E.
Proof.
  introv O. inverts O.
    false* empty_push_inv.
    lets (?&M&?): (eq_push_inv H). subst. auto.
    lets (?&M&?): (eq_push_inv H). subst. auto.
Qed.

Lemma dokt_push_typ_inv : forall E x T,
  dokt (E & x ~ dbind_typ T) -> dwft E T.
Proof.
  introv O. inverts O.
    false* empty_push_inv.
    lets (?&M&?): (eq_push_inv H). subst. false H.
    lets (?&M&?): (eq_push_inv H). subst. inversions~ M.
Qed.

Lemma dwft_ok: forall E t,
    dwft E t ->
    ok E.
Proof.
  introv wf. inductions wf; simpls~.
  pick_fresh y.
  forwards ~ : H0 y.
Qed.

Lemma dwft_dtype: forall E t,
    dwft E t ->
    dtype t.
Proof.
  introv wf. inductions wf; simpls~.
  apply_fresh dtype_all as x.
  apply* H0.
Qed.

Hint Resolve dwft_ok dwft_dtype.

Hint Extern 1 (ok ?E) =>
  match goal with
  | H: dwft _ _ |- _ => apply (dwft_ok H)
  end.

Hint Extern 1 (dtype ?E) =>
  match goal with
  | H: dwft _ _ |- _ => apply (dwft_dtype H)
  end.

Hint Constructors dwft.
Lemma dwft_weakening : forall F x U E v,
    dwft (E & F) U ->
    ok (E & x ~ v & F) ->
    dwft (E & x ~ v & F) U.
Proof.
  introv wf okt. gen v.
  inductions wf; introv okt; auto.
  apply~ dwft_var.
  apply~ binds_weaken.

  apply_fresh dwft_all as x.
  rewrite <- concat_assoc.
  apply~ H0.
  rewrite~ concat_assoc.
  rewrite~ concat_assoc.
Qed.

Lemma dwft_push : forall x U E v,
    dwft E U ->
    ok (E & x ~ v) ->
    dwft (E & x ~ v) U.
Proof.
  intros.
  apply_empty~ dwft_weakening.
Qed.

Lemma dwft_strengthen : forall F E x A v,
    dwft (E & x ~ v & F) A ->
    x \notin dfv_tt A ->
    dwft (E & F) A.
Proof.
  introv wf1 notin.
  inductions wf1; try(constructor~); simpls~.

  apply binds_remove in H0; auto.
  apply~ IHwf1_1.
  apply~ IHwf1_2.

  apply_fresh dwft_all as x.
  rewrite <- concat_assoc.
  apply~ H0.
  rewrite~ concat_assoc.
  apply~ dnotin_fv_tt_open_inv.
  simpls~.
Qed.

Lemma dwft_weaken : forall G T E F,
  dwft (E & G) T ->
  ok (E & F & G) ->
  dwft (E & F & G) T.
Proof.
  intros. gen_eq K: (E & G). gen E F G.
  induction H; intros; subst; eauto.
  (* case: var *)
  apply* dwft_var. apply* binds_weaken.
  (* case: all *)
  apply_fresh* dwft_all as Y. apply_ih_bind* H0.
Qed.


Lemma dwft_strengthen_push : forall E x A v,
    dwft (E & x ~ v) A ->
    x \notin dfv_tt A ->
    dwft (E) A.
Proof.
  intros.
  apply_empty* dwft_strengthen.
Qed.

Lemma dwft_strengthen_typ : forall F E x A v,
    dwft (E & x ~: v & F) A ->
    dwft (E & F) A.
Proof.
  introv wf1.
  inductions wf1; try(constructor~); simpls~.

  tests : (x = x0).
  apply binds_middle_eq_inv in H0; auto.
  inversions H0.
  apply binds_remove in H0; auto.
  apply~ IHwf1_1.
  apply~ IHwf1_2.

  apply_fresh dwft_all as x.
  rewrite <- concat_assoc.
  apply~ H0.
  rewrite~ concat_assoc.
Qed.


Lemma dwft_subst_tb : forall F E T P x,
  dwft (E & x ~tvar & F) T ->
  dwft E P ->
  ok (E & map (dsubst_tb x P) F) ->
  dwft (E & map (dsubst_tb x P) F) (dsubst_tt x P T).
Proof.
  introv WT WP. gen_eq G: (E & x ~tvar & F). gen F.
  induction WT; intros F EQ Ok; subst; simpl dsubst_tt; auto.
  case_var*.
    apply_empty* dwft_weaken.
    destruct (binds_concat_inv H0) as [?|[? ?]].
      apply* dwft_var.
       apply~ binds_concat_right.
       assert (dbind_tvar = dsubst_tb x P dbind_tvar).
       reflexivity. rewrite H2.
       apply~ binds_map.
      destruct (binds_push_inv H2) as [[? ?]|[? ?]].
        subst. false~.
        apply* dwft_var.
  apply_fresh* dwft_all as Y.
   rewrite* dsubst_tt_open_tt_var.
   assert (dbind_tvar = dsubst_tb x P dbind_tvar). reflexivity.
   rewrite H1.
   apply_ih_map_bind* H0.
Qed.


Lemma dokt_strengthen_typ : forall F E x v,
    dokt (E & x ~: v & F) ->
    dokt (E & F).
Proof.
  induction F using env_ind; rew_env_concat; introv Ok.
  rewrite concat_empty_r in *.
  apply dokt_push_inv in Ok; destructs~ Ok.
  rewrite concat_assoc in *.
  destruct v.
  constructor~.
  forwards ~ [? ?] : dokt_push_inv Ok.
  apply* IHF.
  apply dok_from_okt in Ok.
  forwards~ [? ?] : ok_push_inv Ok.
  forwards ~ : dokt_push_typ_inv Ok.
  forwards ~ [? ?] : dokt_push_inv Ok.
  constructor~.
  apply* IHF.
  apply* dwft_strengthen_typ.
Qed.

Lemma dwft_rename : forall E F z u A,
    dwft (E & z ~tvar & F) A ->
    dokt (E & u ~tvar & F) ->
    dwft (E & u ~tvar & F) (dsubst_tt z (dtyp_fvar u) A).
Proof.
  introv wf okt.
  inductions wf; simpls; auto.
  case_var~.
  apply~ dwft_var.
  apply~ binds_middle_eq.
  lets: dok_from_okt okt.
  lets ~ : ok_middle_inv_r H1.

  apply* dwft_var.
  forwards ~ : binds_remove H0.
  apply~ binds_weaken.

  apply_fresh dwft_all as x.
  forwards ~ : H0 x E (F & x ~tvar) z.
  rewrite~ concat_assoc.
  rewrite~ concat_assoc.
  rewrite concat_assoc in H1; auto.
  rewrite <- dsubst_tt_open_tt_var in H1; auto.
Qed.

(** Extraction from a typing assumption in a well-formed environments *)

Lemma dwft_from_env_has_typ : forall x U E,
  dokt E -> binds x (dbind_typ U) E -> dwft E U.
Proof.
  induction E using env_ind; intros Ok B.
  false* binds_empty_inv.
  inversions Ok.
    false (empty_push_inv H0).
    destruct (eq_push_inv H) as [? [? ?]]. subst. clear H.
    apply~ dwft_push.
    apply* IHE.
    destruct (binds_push_inv B) as [[? ?]|[? ?]]. false H2. auto.

    destruct (eq_push_inv H) as [? [? ?]]. subst. clear H.
     destruct (binds_push_inv B) as [[? ?]|[? ?]]. inversions H3.
    apply~ dwft_push.
    apply~ dwft_push.
Qed.

(** Extraction from a well-formed environment *)

Lemma dwft_from_okt_typ : forall x T E,
  dokt (E & x ~ dbind_typ T) -> dwft E T.
Proof.
  intros. inversions* H.
  false (empty_push_inv H1).
  destruct (eq_push_inv H0) as [? [? ?]]. false~ H3.
  destruct (eq_push_inv H0) as [? [? ?]].
  inversion~ H4. subst~.
Qed.


Lemma dokt_subst_tb : forall F E x T,
  dokt (E & x ~tvar & F) ->
  dwft E T ->
  dokt (E & map (dsubst_tb x T) F).
Proof.
 introv O W. induction F using env_ind.
  rewrite map_empty. rewrite concat_empty_r in *.
  lets*: (dokt_push_inv O).
  rewrite map_push. rewrite concat_assoc in *.
  lets (?&?): (dokt_push_inv O).
  destruct v.
  simpls*.
  applys~ dokt_typ. applys* dwft_subst_tb.
  apply* dwft_from_okt_typ.
Qed.


Lemma dwft_open_inv: forall E k T U P,
    dwft E U ->
    dwft E P ->
    dwft E (dopen_tt_rec k U T) ->
    dwft E (dopen_tt_rec k P T).
Proof.
  introv wf1 wf2 wfh.
  inductions wfh.

  destruct T;  simpls~; try(solve[inversion x]).
  case_nat* .

  destruct T;  simpls~; try(solve[inversion x]).
  case_nat* .

  destruct T;  simpls~; try(solve[inversion x]).
  case_nat* .
  inversions x.
  apply~ dwft_var.

  destruct T;  simpls~; try(solve[inversion x]).
  inversions x.
  apply~ dwft_arrow. apply IHwfh1 with U; auto.
  apply IHwfh2 with U; auto.
  case_nat*.

  destruct T;  simpls~; try(solve[inversion x]).
  case_nat* .
  inversions x.
  apply_fresh dwft_all as x.
  unfold dopen_tt.
  rewrite~ dopen_tt_rec_type_commu.
  apply H0 with U; auto.
  apply~ dwft_push.
  apply~ dwft_push.
  unfold dopen_tt.
  rewrite~ dopen_tt_rec_type_commu.
Qed.

Lemma dwft_open_inv_all: forall E T U,
    dwft E U ->
    dwft E (dopen_tt T U) ->
    dwft E (dtyp_all T).
Proof.
  introv wf1 wf2. unfolds dopen_tt.
  apply_fresh dwft_all as x.
  apply dwft_open_inv with U; auto.
  apply~ dwft_push.
  apply~ dwft_push.
Qed.

Lemma dwft_open: forall E T U,
    dwft E U ->
    dwft E (dtyp_all T) ->
    dwft E (dopen_tt T U).
Proof.
  introv wf1 wf2.
  inversions wf2.
  pick_fresh x.
  forwards ~ : H1 x.
  apply dwft_strengthen_push with x dbind_tvar; auto.
  unfolds dopen_tt.
  apply dwft_open_inv with (dtyp_fvar x); auto.
  apply~ dwft_push.
  apply~ dnotin_fv_tt_open_inv.
Qed.

Lemma dwft_notin_env: forall E A y,
    dwft E A ->
    y \notin dom E ->
    y \notin dfv_tt A.
Proof.
  introv wf notin. inductions wf; simpls~.
  apply~ notin_singleton. introv veq. subst~.
  false binds_fresh_inv H0 notin0.
  pick_fresh x.
  forwards~ : H0 x.
  apply* dnotin_fv_tt_dopen.
Qed.

(** Automation *)

Hint Resolve dwft_from_okt_typ.
Hint Immediate dwft_from_env_has_typ.
Hint Resolve dokt_subst_tb dwft_weaken.
Hint Immediate dokt_strengthen_typ.
Hint Resolve dwft_subst_tb.


(** If an environment is well-formed, then its left part is also well-formed. *)

Lemma dokt_concat_left_inv: forall E F,
    dokt (E & F) -> dokt E.
Proof.
  induction F using env_ind; introv okt; auto.
  clean_empty okt; auto.
  rewrite concat_assoc in okt.
  lets [? ?]: dokt_push_inv okt. apply* IHF.
Qed.

(* ********************************************************************** *)
(** * Properties of Closeness *)

(** Abstracting a term name out of a term *)

Fixpoint dclose_ee_rec (k : nat) (z : var) (t : dtrm) {struct t} : dtrm :=
  match t with
  | dtrm_bvar i        => dtrm_bvar i
  | dtrm_fvar x        => If x = z then (dtrm_bvar k) else (dtrm_fvar x)
  | dtrm_nat  i        => dtrm_nat i
  | dtrm_absann t1 t2  => dtrm_absann t1 (dclose_ee_rec (S k) z t2)
  | dtrm_abs t         => dtrm_abs (dclose_ee_rec (S k) z t)
  | dtrm_app t1 t2     => dtrm_app (dclose_ee_rec k z t1) (dclose_ee_rec k z t2)
  | dtrm_let t1 t2     => dtrm_let (dclose_ee_rec k z t1) (dclose_ee_rec (S k) z t2)
  end.

Definition dclose_ee z t := dclose_ee_rec 0 z t.

(** Close var commutes with open with some freshness conditions,
  this is used in the proofs of [close_ee_open] *)

Lemma dclose_ee_rec_open : forall x y z t1 i j,
  i <> j -> y <> x -> y \notin (dfv_ee t1) ->
    (dopen_ee_rec i (dtrm_fvar y) (dopen_ee_rec j (dtrm_fvar z) (dclose_ee_rec j x t1)))
  = (dopen_ee_rec j (dtrm_fvar z) (dclose_ee_rec j x (dopen_ee_rec i  (dtrm_fvar y) t1) )).
Proof.
  induction t1; simpl; intros; try solve [ f_equal* ].
  do 2 (case_nat; simpl); try solve [ case_var* | case_nat* ].
  case_var*. simpl. case_nat*.
Qed.

(** Close var removes fresh var *)

Lemma dclose_ee_fresh : forall x t,
  x \notin dfv_ee (dclose_ee x t).
Proof.
  introv. unfold dclose_ee. generalize 0.
  induction t; intros k; simpls; notin_simpl; auto.
  case_var; simple*.
Qed.

(** Close var is the right inverse of open_var *)

Lemma dclose_ee_open : forall x t,
  dterm t -> t = (dclose_ee x t) dopen_ee_var x.
Proof.
  introv W. unfold dclose_ee, dopen_ee. generalize 0.
  induction W; intros k; simpls; f_equal*.
  case_var*. simpl. case_nat*.
  let L := gather_vars in match goal with |- _ = ?t =>
    destruct (var_fresh (L \u dfv_ee t)) as [y Fr] end.
  apply* (@dopen_ee_rec_inj y).
  unfolds dopen_ee. rewrite* dclose_ee_rec_open.
  let L := gather_vars in match goal with |- _ = ?t =>
    destruct (var_fresh (L \u dfv_ee t)) as [y Fr] end.
  apply* (@dopen_ee_rec_inj y).
  unfolds dopen_ee. rewrite* dclose_ee_rec_open.
  let L := gather_vars in match goal with |- _ = ?t =>
    destruct (var_fresh (L \u dfv_ee t)) as [y Fr] end.
  apply* (@dopen_ee_rec_inj y).
  unfolds dopen_ee. rewrite* dclose_ee_rec_open.
Qed.

(** Abstracting a type name out of a type *)

Fixpoint dclose_tt_rec (k : nat) (z : var) (t : dtyp) {struct t} : dtyp :=
  match t with
  | dtyp_bvar i        => dtyp_bvar i
  | dtyp_unknown       => dtyp_unknown
  | dtyp_fvar x        => If x = z then (dtyp_bvar k) else (dtyp_fvar x)
  | dtyp_nat           => dtyp_nat
  | dtyp_arrow t1 t2   => dtyp_arrow (dclose_tt_rec k z t1) (dclose_tt_rec k z t2)
  | dtyp_all t1        => dtyp_all (dclose_tt_rec (S k) z t1)
  end.

Definition dclose_tt z t := dclose_tt_rec 0 z t.

(** Close var commutes with open with some freshness conditions *)

Lemma dclose_tt_rec_open : forall x y z t1 i j,
  i <> j -> y <> x -> y \notin (dfv_tt t1) ->
    (dopen_tt_rec i (dtyp_fvar y) (dopen_tt_rec j (dtyp_fvar z) (dclose_tt_rec j x t1)))
  = (dopen_tt_rec j (dtyp_fvar z) (dclose_tt_rec j x (dopen_tt_rec i  (dtyp_fvar y) t1) )).
Proof.
  induction t1; simpl; intros; try solve [ f_equal* ].
  do 2 (case_nat; simpl); try solve [ case_var* | case_nat* ].
  case_var*. simpl. case_nat*.
Qed.

(** Close var removes fresh var *)

Lemma dclose_tt_fresh_rec : forall x t k,
  x \notin dfv_tt (dclose_tt_rec k x t).
Proof.
  introv. unfold dclose_tt. gen k.
  induction t; intros k; simpls; notin_simpl; auto.
  case_var; simple*.
Qed.

Lemma dclose_tt_fresh : forall x t,
  x \notin dfv_tt (dclose_tt x t).
Proof.
  unfold dclose_tt.  introv.
  apply dclose_tt_fresh_rec.
Qed.

Hint Resolve dclose_tt_fresh_rec dclose_tt_fresh.

(** Close var is the right inverse of open_var *)

Lemma dclose_tt_open : forall x t k,
  dtype t -> t = dopen_tt_rec k (dtyp_fvar x) (dclose_tt_rec k x t).
Proof.
  introv W. unfold dclose_tt, dopen_tt. gen k.
  induction W; intros k; simpls; f_equal*.
  case_var*. simpl. case_nat*.
  let L := gather_vars in match goal with |- _ = ?t =>
    destruct (var_fresh (L \u dfv_tt t)) as [y Fr] end.
  apply* (@dopen_tt_rec_inj y).
  unfolds dopen_tt. rewrite* dclose_tt_rec_open.
Qed.

Lemma dclose_tt_open_var : forall x t,
  dtype t -> t = dopen_tt (dclose_tt x t) (dtyp_fvar x).
Proof.
  intros. unfolds dopen_tt.
  apply* dclose_tt_open.
Qed.

Lemma dopen_tt_close_fresh : forall y A,
    y \notin dfv_tt A ->
    dclose_tt y (A dopen_tt_var y) = A.
Proof.
  unfolds dopen_tt. unfolds dclose_tt.
  generalize 0. introv. gen n.
  inductions A; introv neq; simpls~;f_equal~.
  case_nat~. simpls~. case_var~.
  case_var~.
Qed.

Hint Resolve dclose_tt_rec_open.
Hint Resolve dclose_tt_open.

(* close does not introduce new free vairables *)

Lemma dnotin_fv_tt_close_inv: forall S x y k,
    x \notin dfv_tt S ->
    x \notin dfv_tt (dclose_tt_rec k y S).
Proof.
  induction S; introv notin; simpls~.
  case_var~. simpls~.
Qed.

Lemma dclose_tt_in_inv : forall x t k y,
        x <> y ->
        x \in dfv_tt (dclose_tt_rec k y t) ->
        x \in dfv_tt t.
Proof.
  introv. unfold dclose_tt. gen k.
  induction t; intros; simpls; notin_simpl; auto.
  rewrite in_union in *. destruct H0. left. apply* IHt1. right. apply* IHt2.
  case_var; simple*.
  simpls. rewrite in_empty in H0. false~.
  apply* IHt.
Qed.

Hint Resolve dnotin_fv_tt_close_inv
.

(** open a closed one is substitution *)

Lemma dclose_tt_open_subst: forall S k x y,
    dtype S ->
    dopen_tt_rec k (dtyp_fvar y) (dclose_tt_rec k x S) = dsubst_tt x (dtyp_fvar y) S.
Proof.
  introv ty. gen k. induction ty; introv; simpls; auto.
  case_var~. simpls. case_nat~.
  rewrite* IHty1. rewrite* IHty2.

  pick_fresh z.
  specializes H0 z (S k).

  rewrite dsubst_tt_open_tt in H0; auto.
  simpls. case_var.

  unfolds dopen_tt.
  unfolds dopen_tt.
  rewrite <- dclose_tt_rec_open in H0; auto.
  apply dopen_tt_rec_inj in H0; auto.
  rewrite~ H0.
  apply dnotin_fv_tt_open_inv; simpls~.
  apply dnotin_fv_tt_subst_inv; simpls~.
Qed.

Hint Resolve dclose_tt_open_subst.

(* ********************************************************************** *)
(** ** Number of All *)

Fixpoint num_of_all (t: dtyp) : nat :=
  match t with
      | dtyp_nat => 0
      | dtyp_unknown => 0
      | dtyp_fvar x => 0
      | dtyp_bvar x => 0
      | dtyp_arrow n1 n2 => (num_of_all n1) + (num_of_all n2)
      | dtyp_all n => 1 + (num_of_all n)
  end.

Lemma num_of_all_mono: forall U,
    dtyp_mono U ->
    num_of_all U = 0.
Proof.
  induction U; introv mn; simpls~.
  inversion~ mn; subst~. rewrite~ IHU1.
  inversion mn.
Qed.

Lemma num_of_all_open_rec_mono: forall S U k,
    dtyp_mono U ->
    num_of_all (dopen_tt_rec k U S) = num_of_all S.
Proof.
  induction S; introv mn; simpls~.
  case_nat~. apply~ num_of_all_mono.
Qed.

Lemma num_of_all_open_mono: forall S U,
    dtyp_mono U ->
    num_of_all (dopen_tt S U) = num_of_all S.
Proof.
  intros. apply* num_of_all_open_rec_mono.
Qed.

Lemma num_of_all_open_rec_unknown: forall S k,
    num_of_all (dopen_tt_rec k dtyp_unknown S) = num_of_all S.
Proof.
  induction S; introv; simpls~.
  case_nat~.
Qed.

Lemma num_of_all_open_unknown: forall S,
    num_of_all (dopen_tt S dtyp_unknown) = num_of_all S.
Proof.
  intros. apply* num_of_all_open_rec_unknown.
Qed.

(* ********************************************************************** *)
(** ** Dtyp Len *)

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

(* ********************************************************************** *)
(** ** Regularity of relations *)

Lemma dsub_regular : forall E A B,
  dsub E A B -> dokt E /\ dwft E A /\ dwft E B.
Proof.
  introv sub.
  inductions sub; try(solve[splits~]).
  destructs~ IHsub1.
  destructs~ IHsub2.

  destructs~ IHsub.
  splits~.
  apply dwft_open_inv_all with tau; auto.

  splits~.
  pick_fresh y. forwards ~ : H0 y.
  destructs H1.
  apply* dokt_concat_left_inv.
  pick_fresh y. forwards ~ : H0 y.
  destructs H1.
  apply* dwft_strengthen_push.

  apply_fresh dwft_all as x.
  forwards ~ : H0 x.
  destructs~ H1.
Qed.

Lemma dconsub_regular : forall E A B,
  dconsub E A B -> dokt E /\ dwft E A /\ dwft E B.
Proof.
  introv sub. inductions sub; auto.
  destructs IHsub1. destructs IHsub2.
  splits~.

  destructs IHsub.
  splits~.
  apply dwft_open_inv_all with tau; auto.

  splits~.
  pick_fresh y. forwards ~ [? [? ?]]: H0 y.
    apply* dokt_concat_left_inv.
  pick_fresh y. forwards ~ [? [? ?]]: H0 y.
    apply* dwft_strengthen_push.
  apply_fresh dwft_all as x.
    forwards ~ [? [? ?]] : H0 x.
Qed.

Lemma dmatch_regular : forall A A1 A2 E,
    dwft E A ->
    dmatch E A A1 A2 ->
    dwft E A1 /\ dwft E A2.
Proof.
  introv wf mat. inductions mat.
  apply~ IHmat.
  inversions wf.
  pick_fresh y.
  apply dwft_strengthen_push with y (dbind_tvar); auto.
  apply dwft_open_inv with (dtyp_fvar y); auto.
  apply~ dwft_push.
  apply~ H3.
  apply~ dnotin_fv_tt_open_inv.

  inversions wf. splits~.
  splits~.
Qed.

Lemma dmatch_regular_inv : forall A A1 A2 E,
    dmatch E A A1 A2 ->
    dwft E A1 -> dwft E A2 ->
    dwft E A.
Proof.
  introv mat wfa1 wfa2. inductions mat; auto.
  apply_fresh dwft_all as x.
  apply dwft_open_inv with tau; auto.
  apply~ dwft_push.
  apply~ dwft_push.
Qed.

Lemma dmatch_regular_dtype : forall A A1 A2 E,
    dmatch E A A1 A2 ->
    dtype A ->
    dtype A1 /\ dtype A2.
Proof.
  introv mat wf. inductions mat.
  apply~ IHmat.
  apply* dtype_open.
  inversions~ wf.
  splits~.
Qed.

Lemma dtyping_regular : forall E e T,
  dtyping E e T -> dokt E /\ dterm e /\ dwft E T.
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

  destructs IHdtyping1.
  destructs IHdtyping2.
  forwards ~ [? ?] : dmatch_regular H0.

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

  destructs IHdtyping.
  splits~.
    apply_fresh dterm_let as y.
    pick_fresh y. specializes H1 y. destructs~ H1.
    specializes H1 y. destructs~ H1.
    pick_fresh y. specializes H1 y. destructs~ H1.
      apply* dwft_strengthen_push.
Qed.

(** Automation *)

Hint Extern 1 (dokt ?E) =>
  match goal with
  | H: dsub _ _ _ |- _ => apply (proj31 (dsub_regular H))
  | H: dconsub _ _ _ |- _ => apply (proj31 (dconsub_regular H))
  | H: dtyping _ _ _ |- _ => apply (proj31 (dtyping_regular H))
  end.

Hint Extern 1 (dterm ?E) =>
  match goal with
  | H: dtyping _ _ _ |- _ => apply (proj32 (dtyping_regular H))
  end.

Hint Extern 1 (dwft ?E ?t) =>
  match goal with
  | H: dsub _ _ _ |- _ => apply (proj32 (dsub_regular H))
  | H: dsub _ _ _ |- _ => apply (proj33 (dsub_regular H))
  | H: dconsub _ _ _ |- _ => apply (proj32 (dconsub_regular H))
  | H: dconsub _ _ _ |- _ => apply (proj33 (dconsub_regular H))
  | H: dmatch _ _ _ _ |- _ => apply (proj21 (dmatch_regular H))
  | H: dmatch _ _ _ _ |- _ => apply (proj22 (dmatch_regular H))
  | H: dtyping _ _ _ |- _ => apply (proj33 (dtyping_regular H))
  end.
