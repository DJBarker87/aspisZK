import JGl_VectorProbe
set_option autoImplicit false
namespace AspisR1.JGl_LeadingPhaseProbe
open Aeneas Aeneas.Std Result FIq_Native
def probe : Result String := do
  let absorbed ← state_only_poseidon.leading_pair_packed_loop ⟨0#usize,poseidon2.RATE⟩ JGl_NumericData.c JGl_NumericData.a
  let external ← state_only_poseidon.external_linear_lazy absorbed
  let c0 ← Array.index_usize poseidon2.EXTERNAL_INITIAL 0#usize
  let c1 ← Array.index_usize poseidon2.EXTERNAL_INITIAL 1#usize
  let powered0 ← state_only_poseidon.full_round_m31_constants_loop ⟨0#usize,poseidon2.POSEIDON2_WIDTH⟩ external c0
  let mid ← state_only_poseidon.external_linear_lazy powered0
  let powered1 ← state_only_poseidon.full_round_m31_constants_loop ⟨0#usize,poseidon2.POSEIDON2_WIDTH⟩ mid c1
  ok (JGl_VectorProbe.format absorbed ++ "\n" ++ JGl_VectorProbe.format external ++ "\n" ++
    JGl_VectorProbe.format powered0 ++ "\n" ++ JGl_VectorProbe.format mid ++ "\n" ++ JGl_VectorProbe.format powered1)
#eval match probe with
  | .ok value => value
  | _ => "failed"
end AspisR1.JGl_LeadingPhaseProbe
