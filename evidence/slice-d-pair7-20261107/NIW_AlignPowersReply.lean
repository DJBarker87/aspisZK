import NIW_AlignFieldReply
import NIT_PowersInstantiation
set_option autoImplicit false
noncomputable section
namespace AspisR1.NIW_AlignPowersReply
open Aeneas Aeneas.Std Result LPi_FieldValues NIT_Cuts

/-- Canonicality belongs to the actual complete emitted powers reply. No
independent powers/log witness is selected by the caller. Native uses are the
already CLOSED counts four and seven. -/
theorem source (n : Usize) (x : E) (cx : canonE x) :
 NIW_AlignFieldReply.Produced (FIo_Native.weights.powers n x) (fun powers=>canonical powers) := by
 obtain ⟨powers,call,model,canonical⟩ := NFW_PowersCohort.source n x cx
 rw [call]
 exact canonical

#print axioms source
end AspisR1.NIW_AlignPowersReply
