import NMT_345ZeroSource
import NMT_R2_ByteEquality
import NMT_R2_EmittedData
set_option autoImplicit false
noncomputable section
namespace NMT_R2_ZeroObservation
open Aeneas Aeneas.Std NMT_345 RSL NMT_R2_EmittedData

theorem law (bytes : Slice U8) (env : Env) :
 RS.ofExcept (requireZero (bytes.val.map byte)) env (observe id (zeroCall bytes)) := by
 rw [zero_value]
 unfold requireZero
 rw [NMT_R2_ByteEquality.zeros]
 cases bytes.val.all (· == 0#u8) <;> rfl
#print axioms law
end NMT_R2_ZeroObservation
end
