Set Implicit Arguments.
Require Import TLC.LibLN DeclDef DeclInfra.
Require Import PBCDef PBCInfra DeclProp.

Inductive pterm_less_precise : ptrm -> ptrm -> Prop :=
  | pterm_less_precise_var : forall x,
      pterm_less_precise (ptrm_fvar x) (ptrm_fvar x)
  | pterm_less_precise_nat : forall i,
      pterm_less_precise (ptrm_nat i) (ptrm_nat i)
  | pterm_less_precise_absann: forall x e1 e2 A1 A2,
      x \notin pfv_ee e1 \u pfv_ee e2 ->
      dtyp_less_precise A1 A2 ->
      pterm_less_precise (e1 popen_ee_var x)
                         (e2 popen_ee_var x) ->
      pterm_less_precise (ptrm_absann A1 e1) (ptrm_absann A2 e2)
  | pterm_less_precise_app : forall e1 e2 e3 e4,
      pterm_less_precise e1 e2 ->
      pterm_less_precise e3 e4 ->
      pterm_less_precise (ptrm_app e1 e3) (ptrm_app e2 e4)
  | pterm_less_precise_cast : forall e1 e2 A1 A2 B1 B2,
      pterm_less_precise e1 e2 ->
      dtyp_less_precise A1 B1 ->
      dtyp_less_precise A2 B2 ->
      pterm_less_precise (ptrm_cast A1 A2 e1) (ptrm_cast B1 B2 e2)
  | pterm_less_precise_tabs: forall x e1 e2,
      x \notin pfv_te e1 \u pfv_te e2 ->
      pterm_less_precise (e1 popen_te_var x)
                         (e2 popen_te_var x) ->
      pterm_less_precise (ptrm_tabs e1) (ptrm_tabs e2)
.
