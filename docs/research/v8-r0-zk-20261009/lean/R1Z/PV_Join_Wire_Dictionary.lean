import R1Z.PV_Join_Wire_ConstantEntries
import R1Z.PV_Join_Wire_Entry3
import R1Z.PV_Join_Wire_Entry71
import R1Z.PV_Join_Wire_Entry72
import R1Z.PV_Join_Wire_Entry77
import R1Z.PV_Join_Wire_Entry80
import R1Z.PV_Join_Wire_Entry84
import R1Z.PV_Join_Wire_Entry100
import R1Z.PV_Join_Wire_Entry101
import R1Z.PV_Join_Wire_Entry105
import R1Z.PV_Join_Wire_Entry107
import R1Z.PV_Join_Wire_Entry109
import R1Z.PV_Join_Wire_Entry110
import R1Z.PV_Join_Wire_Entry118
import R1Z.PV_Join_Wire_Entry120
import R1Z.PV_Join_Wire_Entry127
import R1Z.PV_Join_Wire_Entry128
import R1Z.PV_Join_Wire_Entry130
import R1Z.PV_Join_Wire_Entry131
import R1Z.PV_Join_Wire_Entry225
import R1Z.PV_Join_Wire_Entry229
import R1Z.PV_Join_Wire_Entry246
import R1Z.PV_Join_Wire_Entry51
set_option autoImplicit false
noncomputable section
namespace R1Z.PV_Join_Wire_Dictionary
open Aeneas Aeneas.Std Result ProverRwFull
abbrev native := PV_Join_Wire_Selection.native
/-- Same dictionary expressed by complete extracted source Result functions. -/
def raw (base : ExternalTypes) (ops : @ExternalFuns (native base)) : @ExternalFuns (native base) :=
  letI : ExternalTypes := native base
  {PV_Join_Wire_Selection.installed base ops with
    op3 := PV_Join_Wire_Entry3.source base,
    op71 := PV_Join_Wire_Entry71.source base,
    op72 := PV_Join_Wire_Entry72.source base,
    op77 := PV_Join_Wire_Entry77.source base,
    op80 := PV_Join_Wire_Entry80.source base,
    op82 := PV_Join_Wire_Entry82.source base,
    op83 := PV_Join_Wire_Entry83.source base,
    op84 := PV_Join_Wire_Entry84.source base,
    op86 := PV_Join_Wire_Entry86.source base,
    op100 := PV_Join_Wire_Entry100.source base,
    op101 := PV_Join_Wire_Entry101.source base,
    op105 := PV_Join_Wire_Entry105.source base,
    op107 := PV_Join_Wire_Entry107.source base,
    op109 := PV_Join_Wire_Entry109.source base,
    op110 := PV_Join_Wire_Entry110.source base,
    op111 := PV_Join_Wire_Entry111.source base,
    op114 := PV_Join_Wire_Entry114.source base,
    op118 := PV_Join_Wire_Entry118.source base,
    op120 := PV_Join_Wire_Entry120.source base,
    op127 := PV_Join_Wire_Entry127.source base,
    op128 := PV_Join_Wire_Entry128.source base,
    op130 := PV_Join_Wire_Entry130.source base,
    op131 := PV_Join_Wire_Entry131.source base,
    op225 := PV_Join_Wire_Entry225.source base,
    op229 := PV_Join_Wire_Entry229.source base,
    op246 := PV_Join_Wire_Entry246.source base,
    op51 := PV_Join_Wire_Entry51.source base}
/-- Every listed callback is rewritten by its own exact source-law consumer.
No algebra, canonicality, totality or source/model equation is assumed. -/
theorem dictionary (base : ExternalTypes) (ops : @ExternalFuns (native base)) :
    PV_Join_Wire_Selection.selected base ops =
      @ProverRwOuterGuardLeaves.selected (native base) (raw base ops) := by
  letI : ExternalTypes := native base
  change ProverRwOuterGuardLeaves.selected
    {PV_Join_Wire_Selection.installed base ops with
    op3 := @ExternalFuns.op3 _ (PV_Join_Wire_Selection.selected base ops),
    op71 := @ExternalFuns.op71 _ (PV_Join_Wire_Selection.selected base ops),
    op72 := @ExternalFuns.op72 _ (PV_Join_Wire_Selection.selected base ops),
    op77 := @ExternalFuns.op77 _ (PV_Join_Wire_Selection.selected base ops),
    op80 := @ExternalFuns.op80 _ (PV_Join_Wire_Selection.selected base ops),
    op82 := @ExternalFuns.op82 _ (PV_Join_Wire_Selection.selected base ops),
    op83 := @ExternalFuns.op83 _ (PV_Join_Wire_Selection.selected base ops),
    op84 := @ExternalFuns.op84 _ (PV_Join_Wire_Selection.selected base ops),
    op86 := @ExternalFuns.op86 _ (PV_Join_Wire_Selection.selected base ops),
    op100 := @ExternalFuns.op100 _ (PV_Join_Wire_Selection.selected base ops),
    op101 := @ExternalFuns.op101 _ (PV_Join_Wire_Selection.selected base ops),
    op105 := @ExternalFuns.op105 _ (PV_Join_Wire_Selection.selected base ops),
    op107 := @ExternalFuns.op107 _ (PV_Join_Wire_Selection.selected base ops),
    op109 := @ExternalFuns.op109 _ (PV_Join_Wire_Selection.selected base ops),
    op110 := @ExternalFuns.op110 _ (PV_Join_Wire_Selection.selected base ops),
    op111 := @ExternalFuns.op111 _ (PV_Join_Wire_Selection.selected base ops),
    op114 := @ExternalFuns.op114 _ (PV_Join_Wire_Selection.selected base ops),
    op118 := @ExternalFuns.op118 _ (PV_Join_Wire_Selection.selected base ops),
    op120 := @ExternalFuns.op120 _ (PV_Join_Wire_Selection.selected base ops),
    op127 := @ExternalFuns.op127 _ (PV_Join_Wire_Selection.selected base ops),
    op128 := @ExternalFuns.op128 _ (PV_Join_Wire_Selection.selected base ops),
    op130 := @ExternalFuns.op130 _ (PV_Join_Wire_Selection.selected base ops),
    op131 := @ExternalFuns.op131 _ (PV_Join_Wire_Selection.selected base ops),
    op225 := @ExternalFuns.op225 _ (PV_Join_Wire_Selection.selected base ops),
    op229 := @ExternalFuns.op229 _ (PV_Join_Wire_Selection.selected base ops),
    op246 := @ExternalFuns.op246 _ (PV_Join_Wire_Selection.selected base ops),
    op51 := @ExternalFuns.op51 _ (PV_Join_Wire_Selection.selected base ops)} = _
  unfold raw
  rw [PV_Join_Wire_Entry3.equation base ops, PV_Join_Wire_Entry71.equation base ops, PV_Join_Wire_Entry72.equation base ops, PV_Join_Wire_Entry77.equation base ops, PV_Join_Wire_Entry80.equation base ops, PV_Join_Wire_Entry82.equation base ops, PV_Join_Wire_Entry83.equation base ops, PV_Join_Wire_Entry84.equation base ops, PV_Join_Wire_Entry86.equation base ops, PV_Join_Wire_Entry100.equation base ops, PV_Join_Wire_Entry101.equation base ops, PV_Join_Wire_Entry105.equation base ops, PV_Join_Wire_Entry107.equation base ops, PV_Join_Wire_Entry109.equation base ops, PV_Join_Wire_Entry110.equation base ops, PV_Join_Wire_Entry111.equation base ops, PV_Join_Wire_Entry114.equation base ops, PV_Join_Wire_Entry118.equation base ops, PV_Join_Wire_Entry120.equation base ops, PV_Join_Wire_Entry127.equation base ops, PV_Join_Wire_Entry128.equation base ops, PV_Join_Wire_Entry130.equation base ops, PV_Join_Wire_Entry131.equation base ops, PV_Join_Wire_Entry225.equation base ops, PV_Join_Wire_Entry229.equation base ops, PV_Join_Wire_Entry246.equation base ops, PV_Join_Wire_Entry51.equation base ops]
#print axioms dictionary
end R1Z.PV_Join_Wire_Dictionary
