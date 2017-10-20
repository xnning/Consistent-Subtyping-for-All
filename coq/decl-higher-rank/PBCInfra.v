Set Implicit Arguments.
Require Import LibLN DeclDef.
Require Import PBCDef DeclInfra.

(** Computing free term variables in a term *)

Fixpoint pfv_ee (e : ptrm) {struct e} : vars :=
  match e with
  | ptrm_bvar i       => \{}
  | ptrm_fvar x       => \{x}
  | ptrm_nat i        => \{}
  | ptrm_absann V e1  => (pfv_ee e1)
  | ptrm_app e1 e2    => (pfv_ee e1) \u (pfv_ee e2)
  | ptrm_cast A B e1  => (pfv_ee e1)
  | ptrm_tabs e       => (pfv_ee e)
  end.

Fixpoint pfv_te (e : ptrm) {struct e} : vars :=
  match e with
  | ptrm_bvar i       => \{}
  | ptrm_fvar x       => \{}
  | ptrm_nat i        => \{}
  | ptrm_absann V e1  => (dfv_tt V) \u (pfv_te e1)
  | ptrm_app e1 e2    => (pfv_te e1) \u (pfv_te e2)
  | ptrm_cast A B e1  => (dfv_tt A) \u (dfv_tt B) \u (pfv_te e1)
  | ptrm_tabs e1      => (pfv_te e1)
  end.

(** Substitution for free term variables in terms. *)

Fixpoint psubst_ee (z : var) (u : ptrm) (e : ptrm) {struct e} : ptrm :=
  match e with
  | ptrm_bvar i       => ptrm_bvar i
  | ptrm_fvar x       => If x = z then u else (ptrm_fvar x)
  | ptrm_nat i        => ptrm_nat i
  | ptrm_absann V e1  => ptrm_absann V (psubst_ee z u e1)
  | ptrm_app e1 e2    => ptrm_app (psubst_ee z u e1) (psubst_ee z u e2)
  | ptrm_cast A B e   => ptrm_cast A B (psubst_ee z u e)
  | ptrm_tabs e1      => ptrm_tabs (psubst_ee z u e1)
  end.

Fixpoint psubst_te (z : var) (u : dtyp) (e : ptrm) {struct e} : ptrm :=
  match e with
  | ptrm_bvar i       => ptrm_bvar i
  | ptrm_fvar x       => ptrm_fvar x
  | ptrm_nat i        => ptrm_nat i
  | ptrm_absann V e1  => ptrm_absann (dsubst_tt z u V) (psubst_te z u e1)
  | ptrm_app e1 e2    => ptrm_app (psubst_te z u e1) (psubst_te z u e2)
  | ptrm_cast A B e   => ptrm_cast (dsubst_tt z u A) (dsubst_tt z u B) (psubst_te z u e)
  | ptrm_tabs e1      => ptrm_tabs (psubst_te z u e1)
  end.

Ltac gather_vars :=
  let A := gather_vars_with (fun x : vars => x) in
  let B := gather_vars_with (fun x : var => \{x}) in
  let C := gather_vars_with (fun x : ptrm => pfv_ee x) in
  let D := gather_vars_with (fun x : dtyp => dfv_tt x) in
  let E := gather_vars_with (fun x : denv => dom x) in
  let F := gather_vars_with (fun x : denv => dfv_tt_env x) in
  let G := gather_vars_with (fun x : dtrm => dfv_ee x) in
  let H := gather_vars_with (fun x : ptrm => pfv_te x) in
  constr:(A \u B \u C \u D \u E \u F \u G \u H).

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
(** ** Properties of term substitution in terms *)

Lemma popen_te_rec_term_core : forall e j v u i,
  popen_ee_rec j v e = popen_te_rec i u (popen_ee_rec j v e) ->
  e = popen_te_rec i u e.
Proof.
  induction e; introv H; simpl in *; inversion H; f_equal*; f_equal*.
Qed.

Lemma popen_te_rec_type_core : forall e j v u i, i <> j ->
  popen_te_rec j v e = popen_te_rec i u (popen_te_rec j v e) ->
  e = popen_te_rec i u e.
Proof.
  induction e; introv Neq H; simpl in *; inversion H; f_equal*; f_equal*;
  match goal with H: ?i <> ?j |- ?t = dopen_tt_rec ?i _ ?t =>
   apply* (@dopen_tt_rec_type_core t j) end.
Qed.

Lemma popen_te_rec_term : forall u e,
  pterm e -> forall k, e = popen_te_rec k u e.
Proof.
  induction 1; intros; simpl; f_equal*;
    try solve [ apply* dopen_tt_rec_type ].
  unfolds popen_ee. pick_fresh x.
   apply* (@popen_te_rec_term_core e1 0 (ptrm_fvar x)).
  unfolds popen_te. pick_fresh x.
   apply* (@popen_te_rec_type_core e1 0 (dtyp_fvar x)).
Qed.

Lemma psubst_te_fresh : forall X U e,
  X \notin pfv_te e -> psubst_te X U e = e.
Proof.
  induction e; simpl; intros; f_equal*; autos* dsubst_tt_fresh.
Qed.

(** Substitution distributes on the open operation. *)

Lemma psubst_te_open_te : forall e T X U, dtype U ->
  psubst_te X U (popen_te e T) =
  popen_te (psubst_te X U e) (dsubst_tt X U T).
Proof.
  intros. unfold popen_te. generalize 0.
  induction e; intros; simpls; f_equal*;
  autos* dsubst_tt_open_tt_rec.
Qed.

Lemma psubst_te_open_te_var : forall X Y U e, Y <> X -> dtype U ->
  (psubst_te X U e) popen_te_var Y = psubst_te X U (e popen_te_var Y).
Proof.
  introv Neq Wu. rewrite* psubst_te_open_te.
  simpl. case_var*.
Qed.

Lemma psubst_te_intro : forall X U e,
  X \notin pfv_te e -> dtype U ->
  popen_te e U = psubst_te X U (e popen_te_var X).
Proof.
  introv Fr Wu. rewrite* psubst_te_open_te.
  rewrite* psubst_te_fresh. simpl. case_var*.
Qed.

Lemma popen_ee_rec_term_core : forall e j v u i, i <> j ->
  popen_ee_rec j v e = popen_ee_rec i u (popen_ee_rec j v e) ->
  e = popen_ee_rec i u e.
Proof.
  induction e; introv Neq H; simpl in *; inversion H; f_equal*.
  case_nat*. case_nat*.
Qed.

Lemma popen_ee_rec_type_core : forall e j v u i,
  popen_te_rec j v e = popen_ee_rec i u (popen_te_rec j v e) ->
  e = popen_ee_rec i u e.
Proof.
  induction e; introv H; simpl in *; inversion H; f_equal*.
Qed.

Lemma popen_ee_rec_term : forall u e,
  pterm e -> forall k, e = popen_ee_rec k u e.
Proof.
  induction 1; intros; simpl; f_equal*.
  unfolds popen_ee. pick_fresh x.
   apply* (@popen_ee_rec_term_core e1 0 (ptrm_fvar x)).
  unfolds popen_ee. pick_fresh x.
   apply* (@popen_ee_rec_type_core e1 0 (dtyp_fvar x)).
Qed.

(** Substitution for a fresh name is identity. *)

Lemma psubst_ee_fresh : forall x u e,
  x \notin pfv_ee e -> psubst_ee x u e = e.
Proof.
  induction e; simpl; intros; f_equal*.
  case_var*.
Qed.

(** Substitution distributes on the open operation. *)

Lemma psubst_ee_open_ee : forall t1 t2 u x, pterm u ->
  psubst_ee x u (popen_ee t1 t2) =
  popen_ee (psubst_ee x u t1) (psubst_ee x u t2).
Proof.
  intros. unfold popen_ee. generalize 0.
  induction t1; intros; simpls; f_equal*.
  case_nat*.
  case_var*. rewrite* <- popen_ee_rec_term.
Qed.

(** Substitution and open_var for distinct names commute. *)

Lemma psubst_ee_open_ee_var : forall x y u e, y <> x -> pterm u ->
  (psubst_ee x u e) popen_ee_var y = psubst_ee x u (e popen_ee_var y).
Proof.
  introv Neq Wu. rewrite* psubst_ee_open_ee.
  simpl. case_var*.
Qed.

(** Opening up a body t with a type u is the same as opening
  up the abstraction with a fresh name x and then substituting u for x. *)

Lemma psubst_ee_intro : forall x u e,
  x \notin pfv_ee e -> pterm u ->
  popen_ee e u = psubst_ee x u (e popen_ee_var x).
Proof.
  introv Fr Wu. rewrite* psubst_ee_open_ee.
  rewrite* psubst_ee_fresh. simpl. case_var*.
Qed.

(** Interactions between type substitutions in terms and opening
  with term variables in terms. *)

Lemma psubst_te_open_ee_var : forall x y u e,
  (psubst_te x u e) popen_ee_var y = psubst_te x u (e popen_ee_var y).
Proof.
  introv. unfold popen_ee. generalize 0.
  induction e; intros; simpl; f_equal*. case_nat*.
Qed.

(** Interactions between term substitutions in terms and opening
  with type variables in terms. *)

Lemma psubst_ee_open_te_var : forall x y u e, pterm u ->
  (psubst_ee x u e) popen_te_var y = psubst_ee x u (e popen_te_var y).
Proof.
  introv. unfold popen_te. generalize 0.
  induction e; intros; simpl; f_equal*.
  case_var*. symmetry. autos* popen_te_rec_term.
Qed.

(** Substitutions preserve local closure. *)

Hint Constructors pterm.

Lemma psubst_te_term : forall e Z P,
  pterm e -> dtype P -> pterm (psubst_te Z P e).
Proof.
  lets: dsubst_tt_type. induction 1; intros; simpl; auto.
  apply_fresh* pterm_absann as x. rewrite* psubst_te_open_ee_var.
  apply_fresh* pterm_tabs as x. rewrite* psubst_te_open_te_var.
Qed.

Lemma psubst_ee_term : forall e1 Z e2,
  pterm e1 -> pterm e2 -> pterm (psubst_ee Z e2 e1).
Proof.
  induction 1; intros; simpl; auto.
  case_var*.
  apply_fresh* pterm_absann as y. rewrite* psubst_ee_open_ee_var.
  apply_fresh* pterm_tabs as Y. rewrite* psubst_ee_open_te_var.
Qed.

Lemma pterm_subst : forall t z u,
    pterm t ->
    pterm (psubst_ee z (ptrm_fvar u) t)
.
Proof.
  introv typt.
  apply* psubst_ee_term.
Qed.

Lemma pterm_rename : forall x y S,
  pterm (S popen_ee_var x) ->
  x \notin pfv_ee S ->
  y \notin pfv_ee S ->
  pterm (S popen_ee_var y).
Proof.
  introv Typx Frx Fry.
  tests: (x = y). subst*.
  rewrite~ (@psubst_ee_intro x).
  apply~ pterm_subst.
Qed.

Hint Resolve psubst_ee_term.

(** Open_var with fresh names is an injective operation *)

Lemma popen_ee_rec_inj : forall x t1 t2 k,
  x \notin (pfv_ee t1) -> x \notin (pfv_ee t2) ->
  (popen_ee_rec k (ptrm_fvar x) t1 = popen_ee_rec k (ptrm_fvar x) t2) -> (t1 = t2).
Proof.
  intros x t1.
  induction t1; intros t2 k; destruct t2; simpl; intros; inversion H1;
  try solve [ f_equal*
  | do 2 try case_nat; inversions* H1; try notin_false ].
Qed.

Hint Resolve popen_ee_rec_inj.

Lemma popen_te_rec_inj : forall x t1 t2 k,
  x \notin (pfv_te t1) -> x \notin (pfv_te t2) ->
  (popen_te_rec k (dtyp_fvar x) t1 = popen_te_rec k (dtyp_fvar x) t2) -> (t1 = t2).
Proof.
  intros x t1.
  induction t1; intros t2 k; destruct t2; simpl; intros; inversion H1;
  try solve [ f_equal*
  | do 2 try case_nat; inversions* H1; try notin_false ].
Qed.

Hint Resolve popen_ee_rec_inj.

(* ********************************************************************** *)
(** * Properties of Closeness *)

(** Abstracting a type name out of a term *)

Fixpoint pclose_te_rec (k : nat) (z : var) (t : ptrm) {struct t} : ptrm :=
  match t with
  | ptrm_bvar i        => ptrm_bvar i
  | ptrm_fvar x        => ptrm_fvar x
  | ptrm_nat  i        => ptrm_nat i
  | ptrm_absann t1 t2  => ptrm_absann (dclose_tt_rec k z t1) (pclose_te_rec k z t2)
  | ptrm_app t1 t2     => ptrm_app (pclose_te_rec k z t1) (pclose_te_rec k z t2)
  | ptrm_cast t1 t2 e1 => ptrm_cast (dclose_tt_rec k z t1) (dclose_tt_rec k z t2) (pclose_te_rec k z e1)
  | ptrm_tabs t2       => ptrm_tabs (pclose_te_rec (S k) z t2)
  end.

Definition pclose_te z t := pclose_te_rec 0 z t.

(** Close var commutes with open with some freshness conditions,
  this is used in the proofs of [close_ee_open] *)

Lemma pclose_te_rec_open : forall x y z t1 i j,
  i <> j -> y <> x -> y \notin (pfv_te t1) ->
    (popen_te_rec i (dtyp_fvar y) (popen_te_rec j (dtyp_fvar z) (pclose_te_rec j x t1)))
  = (popen_te_rec j (dtyp_fvar z) (pclose_te_rec j x (popen_te_rec i  (dtyp_fvar y) t1) )).
Proof.
  induction t1; simpl; intros; try solve [ f_equal* ].
Qed.

Lemma pclose_ee_te_rec_open : forall x y z t1 i j,
    (popen_ee_rec i (ptrm_fvar y) (popen_te_rec j (dtyp_fvar z) (pclose_te_rec j x t1)))
  = (popen_te_rec j (dtyp_fvar z) (pclose_te_rec j x (popen_ee_rec i  (ptrm_fvar y) t1) )).
Proof.
  induction t1; simpl; intros; try solve [ f_equal* ].
  case_nat*; simple*.
Qed.

(** Close var removes fresh var *)

Lemma pclose_te_fresh : forall x t,
  x \notin pfv_te (pclose_te x t).
Proof.
  introv. unfold pclose_te. generalize 0.
  induction t; intros k; simpls; notin_simpl; auto.
Qed.

(** Close var is the right inverse of open_var *)

Lemma pclose_te_open : forall x t,
  pterm t -> t = (pclose_te x t) popen_te_var x.
Proof.
  introv W. unfold pclose_te, popen_te. generalize 0.
  induction W; intros k; simpls; f_equal*.

  let L := gather_vars in match goal with |- _ = ?t =>
    destruct (var_fresh (L \u pfv_ee e1 \u pfv_ee t)) as [y Fr] end.
  apply* (@popen_ee_rec_inj y).
  rewrite* pclose_ee_te_rec_open.

  let L := gather_vars in match goal with |- _ = ?t =>
    destruct (var_fresh (L \u pfv_te e1 \u pfv_te t)) as [y Fr] end.
  apply* (@popen_te_rec_inj y).
  rewrite* pclose_te_rec_open.
Qed.


(** Abstracting a term name out of a term *)

Fixpoint pclose_ee_rec (k : nat) (z : var) (t : ptrm) {struct t} : ptrm :=
  match t with
  | ptrm_bvar i        => ptrm_bvar i
  | ptrm_fvar x        => If x = z then (ptrm_bvar k) else (ptrm_fvar x)
  | ptrm_nat  i        => ptrm_nat i
  | ptrm_absann t1 t2  => ptrm_absann t1 (pclose_ee_rec (S k) z t2)
  | ptrm_app t1 t2     => ptrm_app (pclose_ee_rec k z t1) (pclose_ee_rec k z t2)
  | ptrm_cast t1 t2 e1 => ptrm_cast t1 t2 (pclose_ee_rec k z e1)
  | ptrm_tabs t2       => ptrm_tabs (pclose_ee_rec k z t2)
  end.

Definition pclose_ee z t := pclose_ee_rec 0 z t.

(** Close var commutes with open with some freshness conditions,
  this is used in the proofs of [close_ee_open] *)

Lemma pclose_ee_rec_open : forall x y z t1 i j,
  i <> j -> y <> x -> y \notin (pfv_ee t1) ->
    (popen_ee_rec i (ptrm_fvar y) (popen_ee_rec j (ptrm_fvar z) (pclose_ee_rec j x t1)))
  = (popen_ee_rec j (ptrm_fvar z) (pclose_ee_rec j x (popen_ee_rec i  (ptrm_fvar y) t1) )).
Proof.
  induction t1; simpl; intros; try solve [ f_equal* ].
  do 2 (case_nat; simpl); try solve [ case_var* | case_nat* ].
  case_var*. simpl. case_nat*.
Qed.

Lemma pclose_te_ee_rec_open : forall x y z t1 i j,
    (popen_te_rec i (dtyp_fvar y) (popen_ee_rec j (ptrm_fvar z) (pclose_ee_rec j x t1)))
  = (popen_ee_rec j (ptrm_fvar z) (pclose_ee_rec j x (popen_te_rec i  (dtyp_fvar y) t1) )).
Proof.
  induction t1; simpl; intros; try solve [ f_equal* ].
  case_nat*; simple*.
  case_var*; simple*.
  case_nat*; simple*.
Qed.


(** Close var removes fresh var *)

Lemma pclose_ee_fresh : forall x t,
  x \notin pfv_ee (pclose_ee x t).
Proof.
  introv. unfold pclose_ee. generalize 0.
  induction t; intros k; simpls; notin_simpl; auto.
  case_var; simple*.
Qed.

(** Close var is the right inverse of open_var *)

Lemma pclose_ee_open : forall x t,
  pterm t -> t = (pclose_ee x t) popen_ee_var x.
Proof.
  introv W. unfold pclose_ee, popen_ee. generalize 0.
  induction W; intros k; simpls; f_equal*.
  case_var*. simpl. case_nat*.

  let L := gather_vars in match goal with |- _ = ?t =>
    destruct (var_fresh (L \u pfv_ee t)) as [y Fr] end.
  apply* (@popen_ee_rec_inj y).
  unfolds popen_te, popen_ee. rewrite* pclose_ee_rec_open.

  let L := gather_vars in match goal with |- _ = ?t =>
    destruct (var_fresh (L \u pfv_te e1 \u pfv_te t)) as [y Fr] end.
  apply* (@popen_te_rec_inj y).
  unfolds popen_te, popen_ee. rewrite* pclose_te_ee_rec_open.
Qed.


(* ********************************************************************** *)
(** ** Regularity of relations *)

Lemma ptyping_regular : forall E e T,
  ptyping E e T -> dokt E /\ pterm e /\ dwft E T.
Proof.
  induction 1; try(solve[auto;splits~]).
  splits~. apply* dwft_from_env_has_typ.
  splits~.
    pick_fresh y. specializes H0 y. destructs~ H0.
      forwards*: dokt_push_inv.
    apply_fresh pterm_absann as y.
      pick_fresh y. specializes H0 y. destructs~ H0.
      apply dwft_dtype with E; auto.
      apply* dokt_push_typ_inv.
      specializes H0 y. destructs~ H0.
    apply~ dwft_arrow.
      pick_fresh y. specializes H0 y. destructs~ H0.
      apply* dokt_push_typ_inv.
      pick_fresh y. specializes H0 y. destructs~ H0.
      apply* dwft_strengthen_push.

  destructs IHptyping1.
  destructs IHptyping2.
  inversions H3.
  splits~.

  destructs IHptyping.
  splits~.

  splits~.
    pick_fresh y. specializes H0 y. destructs~ H0.
      forwards*: dokt_push_inv.
    apply_fresh pterm_tabs as y.
      specializes H0 y. destructs~ H0.
    apply_fresh dwft_all as y.
      specializes H0 y. destructs~ H0.
Qed.

(** Automation *)

Hint Extern 1 (dokt ?E) =>
  match goal with
  | H: ptyping _ _ _ |- _ => apply (proj31 (ptyping_regular H))
  end.

Hint Extern 1 (pterm ?E) =>
  match goal with
  | H: ptyping _ _ _ |- _ => apply (proj32 (ptyping_regular H))
  end.

Hint Extern 1 (dwft ?E ?t) =>
  match goal with
  | H: ptyping _ _ _ |- _ => apply (proj33 (ptyping_regular H))
  end.
