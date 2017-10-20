Set Implicit Arguments.

Require Import LibLN.
Implicit Types x : var.
Require Import DeclDef.

(** Syntax **)

Inductive ptrm : Set :=
  | ptrm_bvar   : nat -> ptrm
  | ptrm_fvar   : var -> ptrm
  | ptrm_nat    : nat -> ptrm
  | ptrm_absann : dtyp -> ptrm -> ptrm
  | ptrm_app    : ptrm -> ptrm -> ptrm
  | ptrm_cast   : dtyp -> dtyp -> ptrm -> ptrm
  | ptrm_tabs   : ptrm -> ptrm
.

(** Opening up a term binder occuring in a term *)

Fixpoint popen_ee_rec (k : nat) (f : ptrm) (e : ptrm) {struct e} : ptrm :=
  match e with
  | ptrm_bvar i       => If k = i then f else (ptrm_bvar i)
  | ptrm_fvar x       => ptrm_fvar x
  | ptrm_nat i        => ptrm_nat i
  | ptrm_absann V e1  => ptrm_absann V (popen_ee_rec (S k) f e1)
  | ptrm_app e1 e2    => ptrm_app (popen_ee_rec k f e1) (popen_ee_rec k f e2)
  | ptrm_cast A B e1  => ptrm_cast A B (popen_ee_rec k f e1)
  | ptrm_tabs e1      => ptrm_tabs (popen_ee_rec k f e1)
  end.

Definition popen_ee t u := popen_ee_rec 0 u t.

Notation "t 'popen_ee_var' x" := (popen_ee t (ptrm_fvar x)) (at level 67).

Fixpoint popen_te_rec (k : nat) (f : dtyp) (e : ptrm) {struct e} : ptrm :=
  match e with
  | ptrm_bvar i       => ptrm_bvar i
  | ptrm_fvar x       => ptrm_fvar x
  | ptrm_nat i        => ptrm_nat i
  | ptrm_absann V e1  => ptrm_absann (dopen_tt_rec k f V) (popen_te_rec k f e1)
  | ptrm_app e1 e2    => ptrm_app (popen_te_rec k f e1) (popen_te_rec k f e2)
  | ptrm_cast A B e1  => ptrm_cast (dopen_tt_rec k f A) (dopen_tt_rec k f B)
                                  (popen_te_rec k f e1)
  | ptrm_tabs e1      => ptrm_tabs (popen_te_rec (S k) f e1)
  end.

Definition popen_te t u := popen_te_rec 0 u t.

Notation "t 'popen_te_var' x" := (popen_te t (dtyp_fvar x)) (at level 67).

(** Terms as locally closed pre-terms *)

Inductive pterm : ptrm -> Prop :=
  | pterm_var : forall x,
      pterm (ptrm_fvar x)
  | pterm_nat : forall i,
      pterm (ptrm_nat i)
  | pterm_absann : forall L V e1,
      dtype V ->
      (forall x, x \notin L -> pterm (e1 popen_ee_var x)) ->
      pterm (ptrm_absann V e1)
  | pterm_app : forall e1 e2,
      pterm e1 ->
      pterm e2 ->
      pterm (ptrm_app e1 e2)
  | pterm_cast : forall A B e,
      dtype A ->
      dtype B ->
      pterm e ->
      pterm (ptrm_cast A B e)
  | pterm_tabs : forall L e1,
      (forall x, x \notin L -> pterm (e1 popen_te_var x)) ->
      pterm (ptrm_tabs e1)
.

Inductive pcompatible : dtyp -> dtyp -> Prop :=
  | pcompatible_refl: forall A,
      pcompatible A A
  | pcompatible_unknown_r : forall A,
      pcompatible A dtyp_unknown
  | pcompatible_unknown_l : forall A,
      pcompatible dtyp_unknown A
  | pcompatible_arrow : forall A1 A2 B1 B2,
      pcompatible B1 A1 ->
      pcompatible A2 B2 ->
      pcompatible (dtyp_arrow A1 A2) (dtyp_arrow B1 B2)
  | pcompatible_allR: forall L A B,
      (forall x, x \notin L ->
           pcompatible A (B dopen_tt_var x)) ->
      pcompatible A (dtyp_all B)
  | pcompatible_allL: forall A B,
      pcompatible (dopen_tt A dtyp_unknown) B ->
      pcompatible (dtyp_all A) B
.

(** Typing *)

Inductive ptyping : denv -> ptrm -> dtyp -> Prop :=
  | ptyping_var : forall E x T,
      dokt E ->
      binds x (dbind_typ T) E ->
      ptyping E (ptrm_fvar x) T
  | ptyping_nat : forall E i,
      dokt E ->
      ptyping E (ptrm_nat i) (dtyp_nat)
  | ptyping_absann_i : forall L E A B e,
      (forall x, x \notin L ->
            ptyping (E & x ~: A) (e popen_ee_var x) B) ->
      ptyping E (ptrm_absann A e) (dtyp_arrow A B)
  | ptyping_app : forall E e1 e2 A1 A2,
      ptyping E e1 (dtyp_arrow A1 A2) ->
      ptyping E e2 A1 ->
      ptyping E (ptrm_app e1 e2) A2
  | ptyping_cast : forall E e A B,
      ptyping E e A ->
      dwft E B ->
      pcompatible A B ->
      ptyping E (ptrm_cast A B e) B
  | ptyping_tabs : forall L E A e,
      (forall a, a \notin L ->
            ptyping (E & a ~tvar) (e popen_te_var a) (A dopen_tt_var a)) ->
      ptyping E (ptrm_tabs e) (dtyp_all A)
.