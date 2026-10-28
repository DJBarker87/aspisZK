import R1Z.PV_CB_TakeSource
import R1Z.PV_CB_Op71Exact
import R1Z.PV_CB_Op72Exact
import R1Z.PV_CB_Op77Source
import R1Z.PV_CB_Op80Exact
import R1Z.PV_CB_Op82Source
import R1Z.PV_CB_Op83Source
import R1Z.PV_CB_Op84Exact
import R1Z.PV_CB_Op86Source
import R1Z.PV_CB_Op100Exact
import R1Z.PV_CB_Op101Exact
import R1Z.PV_CB_Op105Exact
import R1Z.PV_CB_Op107Exact
import R1Z.PV_CB_Op109Exact
import R1Z.PV_CB_Op110Source
import R1Z.PV_CB_Op111Source
import R1Z.PV_CB_Op114Source
import R1Z.PV_CB_Op118Exact
import R1Z.PV_CB_Op127Source
import R1Z.PV_CB_Op128Source
import R1Z.PV_CB_Op130Source
import R1Z.PV_CB_Op131Source
import R1Z.PV_CB_Op229Source
set_option autoImplicit false
noncomputable section
namespace R1Z.PV_CB_CandidateDictionary
open Aeneas Aeneas.Std Result ProverRwFull
abbrev native := PV_CB_Op229Transport.native
abbrev Late := PV_CB_Op229Transport.Late
/-- Prepared joint value/source selection. Open callbacks remain supplied by ops.
    This is not a RunJoin or a privacy endpoint theorem. -/
@[reducible] def selected (base : ExternalTypes) (ops : @ExternalFuns (native base)) :
    @ExternalFuns (native base) :=
  letI : ExternalTypes := native base
  {ops with
    op3 := @ExternalFuns.op3 _ (PV_CB_Take.selected ops),
    op71 := @ExternalFuns.op71 _ (PV_CB_Op71Exact.selected ops),
    op72 := @ExternalFuns.op72 _ (PV_CB_Op72Exact.selected ops),
    op77 := @ExternalFuns.op77 _ (PV_CB_PointClone.selected ops),
    op80 := @ExternalFuns.op80 _ (PV_CB_Op80Exact.selected ops),
    op82 := @ExternalFuns.op82 _ (PV_CB_Merkle.selected ops),
    op83 := @ExternalFuns.op83 _ (PV_CB_Merkle.selected ops),
    op84 := @ExternalFuns.op84 _ (PV_CB_Op84Exact.selected ops),
    op86 := @ExternalFuns.op86 _ (PV_CB_Merkle.selected ops),
    op100 := @ExternalFuns.op100 _ (PV_CB_Op100Exact.selected ops),
    op101 := @ExternalFuns.op101 _ (PV_CB_Op101Exact.selected ops),
    op105 := @ExternalFuns.op105 _ (PV_CB_Op105Exact.selected ops),
    op107 := @ExternalFuns.op107 _ (PV_CB_Op107Exact.selected ops),
    op109 := @ExternalFuns.op109 _ (PV_CB_Op109Exact.selected ops),
    op110 := @ExternalFuns.op110 _ (PV_CB_Op110Source.selected ops),
    op111 := @ExternalFuns.op111 _ (PV_CB_State.selected ops),
    op114 := @ExternalFuns.op114 _ (PV_CB_Op114Source.selected ops),
    op118 := @ExternalFuns.op118 _ (PV_CB_Op118Exact.selected ops),
    op127 := @ExternalFuns.op127 _ (PV_CB_Borrow.selected ops),
    op128 := @ExternalFuns.op128 _ (PV_CB_Borrow.selected ops),
    op130 := @ExternalFuns.op130 _ (PV_CB_Borrow.selected ops),
    op131 := @ExternalFuns.op131 _ (PV_CB_Borrow.selected ops),
    op229 := @ExternalFuns.op229 _ (PV_CB_Op229Source.selected base ops)}
end R1Z.PV_CB_CandidateDictionary
