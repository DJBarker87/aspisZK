import JGl_NumericData
import FIq_Native07
set_option autoImplicit false
namespace AspisR1.JGl_VectorProbe
open Aeneas Aeneas.Std Result FIq_Native
def format {N : Usize} (a : Array field.QM31 N) : String :=
  String.intercalate ";" (a.val.map (fun (q : field.QM31)=>
    toString q.c0.a.val ++ "," ++ toString q.c0.b.val ++ "," ++ toString q.c1.a.val ++ "," ++ toString q.c1.b.val))
def probe : Result String := do
  let absorbed ← state_only_poseidon.leading_pair_packed_loop ⟨0#usize,poseidon2.RATE⟩ JGl_NumericData.c JGl_NumericData.a
  let external ← state_only_poseidon.external_linear_lazy absorbed
  let c0 ← Array.index_usize poseidon2.EXTERNAL_INITIAL 0#usize
  let c1 ← Array.index_usize poseidon2.EXTERNAL_INITIAL 1#usize
  let mid ← state_only_poseidon.full_round_m31_constants external c0
  let lead ← state_only_poseidon.full_round_m31_constants mid c1
  let w : Array field.QM31 3#usize := ⟨[
    JGl_NumericData.low.val[1]'(by decide),JGl_NumericData.low.val[9]'(by decide),JGl_NumericData.low.val[10]'(by decide)],by rfl⟩
  let i2 ← Array.index_usize poseidon2.EXTERNAL_INITIAL 2#usize
  let i3 ← Array.index_usize poseidon2.EXTERNAL_INITIAL 3#usize
  let f0 ← Array.index_usize poseidon2.EXTERNAL_FINAL 0#usize
  let f1 ← Array.index_usize poseidon2.EXTERNAL_FINAL 1#usize
  let f2 ← Array.index_usize poseidon2.EXTERNAL_FINAL 2#usize
  let f3 ← Array.index_usize poseidon2.EXTERNAL_FINAL 3#usize
  let even ← state_only_poseidon.interpolate_three_constant_columns w i2 f0 f2
  let odd ← state_only_poseidon.interpolate_three_constant_columns w i3 f1 f3
  let midFull ← state_only_poseidon.full_round JGl_NumericData.a even
  let full ← state_only_poseidon.full_round midFull odd
  ok (format lead ++ "\n" ++ format full)
#eval match probe with
  | .ok value => value
  | _ => "failed"
end AspisR1.JGl_VectorProbe
