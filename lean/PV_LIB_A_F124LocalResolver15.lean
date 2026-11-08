import PV_LIB_A_Full124TableGap14
import PV_FN_THREAD_f124_Continuation
set_option autoImplicit false
noncomputable section
namespace PV_LIB_A_F124LocalResolver15
open PV_STX2_Syntax
open PV_LIB_A_Full124TableGap14

/-- Literal dispositions used by CLOSED124's local constructor layer. These
are source-table equations, independent of all entry stores and native replies. -/
structure Bindings (bodies : Nat → Option PV_STX2_SliceSyntax.Program) : Prop where
  body216 : bodies 216 = some PV_THR2_F216.live
  body218 : bodies 218 = some PV_THR2_F218.live
  body315 : bodies 315 = some PV_THR2_F315.live
  native121 : bodies 121 = none
  native217 : bodies 217 = none
  native312 : bodies 312 = none
  native313 : bodies 313 = none

/-- The local CLOSED constructor table does not change a Full-compatible
regular resolver. This removes this particular table replacement only;
PacketOriginalTable, the installed handler and context-history transport
still require their own proofs before a lane-C join can be credited. -/
theorem fixed (bodies : Nat → Option PV_STX2_SliceSyntax.Program)
    (traits : Data → Option PV_STX2_SliceSyntax.Program) (h : Bindings bodies) :
    PV_THR2_PacketConstructorLocalTable.table (fullRegular bodies traits) =
      fullRegular bodies traits := by
  funext d
  unfold PV_THR2_PacketConstructorLocalTable.table
  split <;> simp_all [fullRegular, h.body216, h.body218, h.body315,
    h.native121, h.native217, h.native312, h.native313]

#print axioms fixed
end PV_LIB_A_F124LocalResolver15
