Set Implicit Arguments.
Require Import TLC.LibLN DeclDef DeclInfra.
Require Import PBCDef PBCInfra DeclProp.

Inductive pterm_less_precise : denv -> denv -> ptrm -> ptrm -> Prop :=
  | pterm_less_precise_var : forall E F x A B,
      dokt E -> dokt F ->
      binds x A E ->
      binds x B F ->
      pterm_less_precise E F (ptrm_fvar x) (ptrm_fvar x)
  | pterm_less_precise_nat : forall E F i,
      dokt E -> dokt F ->
      pterm_less_precise E F(ptrm_nat i) (ptrm_nat i)
  | pterm_less_precise_absann: forall x E F e1 e2 A1 A2,
      dtyp_less_precise A1 A2 ->
      x \notin dfv_tt_env E \u dfv_tt A1 \u dfv_tt A2 \u pfv_ee e1 \u pfv_ee e2 ->
      pterm_less_precise (E & x ~: A1) (F & x ~: A2)
                         (e1 popen_ee_var x)
                         (e2 popen_ee_var x) ->
      pterm_less_precise E F (ptrm_absann A1 e1) (ptrm_absann A2 e2)
  | pterm_less_precise_app : forall E F e1 e2 e3 e4,
      pterm_less_precise E F e1 e2 ->
      pterm_less_precise E F e3 e4 ->
      pterm_less_precise E F (ptrm_app e1 e3) (ptrm_app e2 e4)
  | pterm_less_precise_cast : forall E F e1 e2 A1 A2 B1 B2,
      pterm_less_precise E F e1 e2 ->
      dtyp_less_precise A1 B1 ->
      dtyp_less_precise A2 B2 ->
      pterm_less_precise E F (ptrm_cast A1 A2 e1) (ptrm_cast B1 B2 e2)
  | pterm_less_precise_cast_l : forall E F e1 e2 A1 A2 B,
      pterm_less_precise E F e1 e2 ->
      ptyping F e2 B ->
      dtyp_less_precise A1 B ->
      dtyp_less_precise A2 B ->
      pterm_less_precise E F (ptrm_cast A1 A2 e1) e2
  | pterm_less_precise_cast_r : forall E F e1 e2 A B1 B2,
      pterm_less_precise E F e1 e2 ->
      ptyping E e1 A ->
      dtyp_less_precise A B1 ->
      dtyp_less_precise A B2 ->
      pterm_less_precise E F e1 (ptrm_cast B1 B2 e2)
  | pterm_less_precise_tabs: forall x E F e1 e2,
      x \notin dfv_tt_env E \u pfv_te e1 \u pfv_te e2 ->
      pterm_less_precise (E & x ~tvar) (F & x ~tvar)
                         (e1 popen_te_var x)
                         (e2 popen_te_var x) ->
      pterm_less_precise E F (ptrm_tabs e1) (ptrm_tabs e2)
.
