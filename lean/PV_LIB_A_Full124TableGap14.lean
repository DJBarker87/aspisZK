import PV_LIB_A_V2PrefixTables14
import PV_THR2_F124
set_option autoImplicit false
namespace PV_LIB_A_Full124TableGap14
open PV_STX2_Syntax PV_LIB_A_StructuredFrontier13

/-- Exact outer regular-BODY dispatch shape of lane C's frozen Full.programs
(read-only F361Full.lean, pinned in session14/LANE_C_LATEST_INPUT.json).
Its trait fallback is irrelevant at this regular124 descriptor. -/
def fullRegular (bodies : Nat → Option PV_STX2_SliceSyntax.Program)
    (traits : Data → Option PV_STX2_SliceSyntax.Program) (fn : Data) :=
  match PV_THR2_OffPath.functionId fn with
  | some id => bodies id
  | none => traits fn

theorem at124 (bodies : Nat → Option PV_STX2_SliceSyntax.Program)
    (traits : Data → Option PV_STX2_SliceSyntax.Program)
    (body124 : bodies 124 = some PV_THR2_F124.live) :
    fullRegular bodies traits (fn PV_LIB_A_PrefixNativeCalls14.src124) = some PV_THR2_F124.live := body124

/-- CHECKED composition obstruction, not a negation of OwnInit's complete
premises. The old opaque-124 lookup bundle cannot instantiate the full table.
Use CLOSED124 at BODY entry with its explicit Post store and prove transport. -/
theorem not_prefix_tables (bodies : Nat → Option PV_STX2_SliceSyntax.Program)
    (traits : Data → Option PV_STX2_SliceSyntax.Program)
    (body124 : bodies 124 = some PV_THR2_F124.live) :
    ¬ PV_LIB_A_V2PrefixTables14.Tables (fullRegular bodies traits) := by
  intro impossible
  have h := impossible.native124
  rw [at124 bodies traits body124] at h
  cases h

#print axioms at124
#print axioms not_prefix_tables
end PV_LIB_A_Full124TableGap14
