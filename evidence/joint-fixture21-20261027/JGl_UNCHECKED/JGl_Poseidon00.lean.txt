import JGl_WordProof
import JGl_NumericData
import FJh_Native07RawValue
set_option autoImplicit false
noncomputable section
namespace AspisR1.JGl_Poseidon00
open FIw_ArrayValue (decoded)
/-- One packed output of the finite Native07 mathematical VALUE. This uses
memoized, individually certified word operations, not source-loop reduction. -/
theorem value : FJh_Native07RawValue.model JGl_NumericData.openings JGl_NumericData.sops ⟨0,by decide⟩=
    decoded JGl_NumericData.poseidon ⟨0,by decide⟩ := by
  jgl_words
#print axioms value
end AspisR1.JGl_Poseidon00
end
