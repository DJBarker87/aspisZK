import RPu_FIq_Native07
import RPv_FJa_PoseidonOrigins
set_option autoImplicit false
noncomputable section
namespace AspisR1.NKG_OracleFactor
open Aeneas Aeneas.Std Result FIq_Native
open FIv_NativeArithmetic (NQ)
open FJa_PoseidonOrigins (Openings Selectors NP fullFold internalFold)
/-- Source-ordered stages of the emitted deterministic evaluator. All operations
are the literal installed operations; there is no Ops-dictionary parameter. -/
def source (o : Openings) (s : Selectors) : Result (Array NQ 4#usize) := do
 let leadingLow ← Array.index_usize s.local 0#usize
 let fullLow ← fullFold s
 let internalLow ← internalFold s
 let lead ← state_only_poseidon.leading_pair_packed o
 let full ← state_only_poseidon.interpolated_full_pair_packed o.z s.local
 let internal ← state_only_poseidon.interpolated_internal_pair o.z s.local
 let p ← FIq_Native.core.array.Array.map (BuiltinFnMut NQ NP)
   (Array.make 3#usize [leadingLow,fullLow,internalLow]) field.PreparedQm31Multiplier.new
 let block ← field.PreparedQm31Multiplier.new s.block
 array_from_fn_copy 4#usize field.QM31.Insts.CoreMarkerCopy
   state_only_poseidon.evaluate_state_only_poseidon_oracle_projected.closure_2.Insts.CoreOpsFunctionFnMutTupleUsizeQM31
   field.QM31.ZERO (o,internal,block,p,lead,full)
theorem factor (o : Openings) (s : Selectors) :
 state_only_poseidon.evaluate_state_only_poseidon_oracle_projected o s=source o s := by
 simp only [state_only_poseidon.evaluate_state_only_poseidon_oracle_projected,source,fullFold,internalFold,bind_assoc_eq]
#print factor
#print axioms factor
end AspisR1.NKG_OracleFactor
end
