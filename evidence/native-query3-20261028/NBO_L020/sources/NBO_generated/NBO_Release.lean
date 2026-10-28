import NBO_TopInstall
import NBO_GeometryDomain
set_option autoImplicit false
noncomputable section
namespace NBO_Release
open Aeneas Aeneas.Std Result AspisR1 AspisR1Stage2 Port3_NativeQueryBody
/-- Release trace/observer installation preserves every lower operation law. -/
theorem lower (ops : Ops) (laws : NBO_QueryDomains.Lower ops) :
 NBO_QueryDomains.Lower (Port3_QueryStage.release ops) :=
 ⟨laws.decode,laws.fromFn,laws.inverse,laws.line⟩
theorem fields (ops : Ops) (laws : NBO_TailDomain.NBC_Fields ops) :
 NBO_TailDomain.NBC_Fields (Port3_QueryStage.release ops) :=
 ⟨laws.product,laws.sum,laws.power⟩
/-- Reuse the actual retained source-shaped mark definition at None. -/
theorem mark_none (ops : Ops) (phase : verifier.Phase) :
 (Port3_QueryStage.release ops).op19
   none phase=ok () := by
 exact Port3_QueryStage.mark_none phase
#print axioms lower
#print axioms fields
#print axioms mark_none
end NBO_Release
end
