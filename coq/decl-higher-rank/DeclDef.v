Set Implicit Arguments.

Require Import LibLN.
Implicit Types x : var.

(** Syntax **)

Inductive dtyp : Set :=
  | dtyp_nat : dtyp
  | dtyp_arrow : dtyp -> dtyp -> dtyp
  | dtyp_unknown : dtyp
  | dtyp_bvar  : nat -> dtyp
  | dtyp_fvar  : var -> dtyp
  | dtyp_all   : dtyp -> dtyp
.

Inductive dtrm : Set :=
  | dtrm_bvar   : nat -> dtrm
  | dtrm_fvar   : var -> dtrm
  | dtrm_nat    : nat -> dtrm
  | dtrm_absann : dtyp -> dtrm -> dtrm
  | dtrm_app    : dtrm -> dtrm -> dtrm
  | dtrm_abs    : dtrm -> dtrm
.

(** Opening up a type binder occuring in a type *)

Fixpoint dopen_tt_rec (K : nat) (U : dtyp) (T : dtyp) {struct T} : dtyp :=
  match T with
  | dtyp_nat         => dtyp_nat
  | dtyp_unknown     => dtyp_unknown
  | dtyp_bvar J      => If K = J then U else (dtyp_bvar J)
  | dtyp_fvar X      => dtyp_fvar X
  | dtyp_arrow T1 T2 => dtyp_arrow (dopen_tt_rec K U T1) (dopen_tt_rec K U T2)
  | dtyp_all T       => dtyp_all (dopen_tt_rec (S K) U T)
  end.

Definition dopen_tt T U := dopen_tt_rec 0 U T.

(** Opening up a term binder occuring in a term *)

Fixpoint dopen_ee_rec (k : nat) (f : dtrm) (e : dtrm) {struct e} : dtrm :=
  match e with
  | dtrm_bvar i       => If k = i then f else (dtrm_bvar i)
  | dtrm_fvar x       => dtrm_fvar x
  | dtrm_nat i        => dtrm_nat i
  | dtrm_absann V e1  => dtrm_absann V (dopen_ee_rec (S k) f e1)
  | dtrm_app e1 e2    => dtrm_app (dopen_ee_rec k f e1) (dopen_ee_rec k f e2)
  | dtrm_abs e1       => dtrm_abs (dopen_ee_rec (S k) f e1)
  end.

Definition dopen_ee t u := dopen_ee_rec 0 u t.

(** Notation for opening up binders with type or term variables *)

Notation "T 'dopen_tt_var' X" := (dopen_tt T (dtyp_fvar X)) (at level 67).

Notation "t 'dopen_ee_var' x" := (dopen_ee t (dtrm_fvar x)) (at level 67).

(** Types as locally closed pre-types *)

Inductive dtype : dtyp -> Prop :=
  | dtype_nat :
      dtype dtyp_nat
  | dtype_unknown :
      dtype dtyp_unknown
  | dtype_var : forall X,
      dtype (dtyp_fvar X)
  | dtype_arrow : forall T1 T2,
      dtype T1 ->
      dtype T2 ->
      dtype (dtyp_arrow T1 T2)
  | dtype_all : forall L T2,
      (forall X, X \notin L -> dtype (T2 dopen_tt_var X)) ->
      dtype (dtyp_all T2).

(** Terms as locally closed pre-terms *)

Inductive dterm : dtrm -> Prop :=
  | dterm_var : forall x,
      dterm (dtrm_fvar x)
  | dterm_nat : forall i,
      dterm (dtrm_nat i)
  | dterm_absann : forall L V e1,
      dtype V ->
      (forall x, x \notin L -> dterm (e1 dopen_ee_var x)) ->
      dterm (dtrm_absann V e1)
  | dterm_abs : forall L e1,
      (forall x, x \notin L -> dterm (e1 dopen_ee_var x)) ->
      dterm (dtrm_abs e1)
  | dterm_app : forall e1 e2,
      dterm e1 ->
      dterm e2 ->
      dterm (dtrm_app e1 e2)
.

(** Environment is an associative list of bindings. *)

Inductive dbind : Set :=
  | dbind_tvar : dbind
  | dbind_typ : dtyp -> dbind
.

Definition denv := LibEnv.env dbind.

Notation "x ~tvar" := (x ~ dbind_tvar)
  (at level 23, left associativity) : env_scope.
Notation "x ~: T" := (x ~ dbind_typ T)
  (at level 23, left associativity) : env_scope.

(** A type T is well formed under environment E *)

Inductive dwft : denv -> dtyp -> Prop :=
  | dwft_nat : forall E,
      ok E ->
      dwft E dtyp_nat
  | dwft_unknown : forall E,
      ok E ->
      dwft E dtyp_unknown
  | dwft_var : forall E x,
      ok E ->
      binds x dbind_tvar E ->
      dwft E (dtyp_fvar x)
  | dwft_arrow : forall E A1 A2,
      dwft E A1 ->
      dwft E A2 ->
      dwft E (dtyp_arrow A1 A2)
  | dwft_all : forall L E A,
      (forall X, X \notin L ->
            dwft (E & X ~tvar) (A dopen_tt_var X)) ->
      dwft E (dtyp_all A)
.

(** A environment E is well-formed if it contains no duplicate bindings and well-foremd types *)

Inductive dokt : denv -> Prop :=
  | dokt_empty :
      dokt empty
  | dokt_tvar : forall E x,
      dokt E -> x # E -> dokt (E & x ~tvar)
  | dokt_typ : forall E x A,
      dokt E -> x # E ->
      dwft E A ->
      dokt (E & x ~: A)
.

(** mono type : contains no unknown type or quantifier *)

Inductive dtyp_mono : dtyp -> Prop :=
  | dtyp_mono_nat:
      dtyp_mono dtyp_nat
  | dtyp_mono_var: forall x,
      dtyp_mono (dtyp_fvar x)
  | dtyp_mono_arrow: forall A B,
      dtyp_mono A ->
      dtyp_mono B ->
      dtyp_mono (dtyp_arrow A B)
.

(** Matching *)

Inductive dmatch : denv -> dtyp -> dtyp -> dtyp -> Prop :=
  | dmatch_all : forall E A A1 A2 tau,
      dtyp_mono tau ->
      dwft E tau ->
      dmatch E (dopen_tt A tau) A1 A2 ->
      dmatch E (dtyp_all A) A1 A2
  | dmatch_arrow : forall E A1 A2,
      dmatch E (dtyp_arrow A1 A2) A1 A2
  | dmatch_unknown : forall E,
      dmatch E dtyp_unknown dtyp_unknown dtyp_unknown
.

(** Subtyping *)

Inductive dsub : denv -> dtyp -> dtyp -> Prop :=
  | dsub_nat : forall E,
      dokt E ->
      dsub E dtyp_nat dtyp_nat
  | dsub_var : forall E x,
      dokt E ->
      binds x dbind_tvar E ->
      dsub E (dtyp_fvar x) (dtyp_fvar x)
  | dsub_unknown : forall E,
      dokt E ->
      dsub E dtyp_unknown dtyp_unknown
  | dsub_fun : forall E A1 A2 B1 B2,
      dsub E B1 A1 ->
      dsub E A2 B2 ->
      dsub E (dtyp_arrow A1 A2) (dtyp_arrow B1 B2)
  | dsub_allL : forall E A B tau,
      dtyp_mono tau ->
      dwft E tau ->
      dsub E (dopen_tt A tau) B ->
      dsub E (dtyp_all A) B
  | dsub_allR : forall L E A B,
      (forall x, x \notin L ->
            dsub (E & x ~tvar) A (B dopen_tt_var x)) ->
      dsub E A (dtyp_all B)
.

(** Consistent Subtyping *)

Inductive dconsub : denv -> dtyp -> dtyp -> Prop :=
  | dconsub_nat : forall E,
      dokt E ->
      dconsub E dtyp_nat dtyp_nat
  | dconsub_var : forall E x,
      dokt E ->
      binds x dbind_tvar E ->
      dconsub E (dtyp_fvar x) (dtyp_fvar x)
  | dconsub_unknown_l : forall E A,
      dokt E ->
      dwft E A ->
      dconsub E dtyp_unknown A
  | dconsub_unknown_r : forall E A,
      dokt E ->
      dwft E A ->
      dconsub E A dtyp_unknown
  | dconsub_fun : forall E A1 A2 B1 B2,
      dconsub E B1 A1 ->
      dconsub E A2 B2 ->
      dconsub E (dtyp_arrow A1 A2) (dtyp_arrow B1 B2)
  | dconsub_allL : forall E A B tau,
      dtyp_mono tau ->
      dwft E tau ->
      dconsub E (dopen_tt A tau) B ->
      dconsub E (dtyp_all A) B
  | dconsub_allR : forall L E A B,
      (forall x, x \notin L ->
            dconsub (E & x ~tvar) A (B dopen_tt_var x)) ->
      dconsub E A (dtyp_all B)
.

(** Typing *)

Inductive dtyping : denv -> dtrm -> dtyp -> Prop :=
  | dtyping_var : forall E x T,
      dokt E ->
      binds x (dbind_typ T) E ->
      dtyping E (dtrm_fvar x) T
  | dtyping_nat : forall E i,
      dokt E ->
      dtyping E (dtrm_nat i) (dtyp_nat)
  | dtyping_absann : forall L E A B e,
      dwft empty A -> (* type annotations are closed *)
      (forall x, x \notin L ->
            dtyping (E & x ~: A) (e dopen_ee_var x) B) ->
      dtyping E (dtrm_absann A e) (dtyp_arrow A B)
  | dtyping_app : forall E e1 e2 A A1 A2 A3,
      dtyping E e1 A ->
      dmatch E A A1 A2 ->
      dtyping E e2 A3 ->
      dconsub E A3 A1 ->
      dtyping E (dtrm_app e1 e2) A2
  | dtyping_abs : forall L E A B e,
      dtyp_mono A ->
      (forall x, x \notin L ->
            dtyping (E & x ~: A) (e dopen_ee_var x) B) ->
      dtyping E (dtrm_abs e) (dtyp_arrow A B)
  | dtyping_gen : forall L E A e,
      (forall a, a \notin L ->
            dtyping (E & a ~tvar) e (A dopen_tt_var a)) ->
      dtyping E e (dtyp_all A)
.

(** Consistent *)

Inductive dconsist: dtyp -> dtyp -> Prop :=
  | dconsist_refl: forall A,
      dconsist A A
  | dconsist_unknown_r: forall A,
      dconsist A dtyp_unknown
  | dconsist_unknown_l: forall A,
      dconsist dtyp_unknown A
  | dconsist_arrow: forall A1 A2 B1 B2,
      dconsist A1 B1 ->
      dconsist A2 B2 ->
      dconsist (dtyp_arrow A1 A2) (dtyp_arrow B1 B2)
  | dconsist_all: forall A B,
      dconsist A B ->
      dconsist (dtyp_all A) (dtyp_all B)
.

