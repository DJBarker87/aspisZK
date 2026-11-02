import R1Z.PV_RunJoin_WideLimbsParse72
import R1Z.PV_RunJoin_PolyCell38
set_option autoImplicit false
namespace R1Z.PV_RunJoin_PolyCellCanonical72
open Aeneas Aeneas.Std ProverRwFull
abbrev Q := aspis_core.field.QM31

theorem complete (q : Q) :
    PV_RunJoin_WideLimbsParse72.Canonical (PV_RunJoin_PolyCell38.wide q) := by
  have h := ProverCommitNativeOps47.normalize_canonical (PV_RunJoin_FieldData34.old q)
  exact ⟨h.1.1,h.1.2,h.2.1,h.2.2,by decide,by decide,by decide,by decide⟩

#print axioms complete
end R1Z.PV_RunJoin_PolyCellCanonical72
