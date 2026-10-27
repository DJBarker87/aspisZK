import RPv_FJe_PackedLoopCanonical
set_option autoImplicit false
noncomputable section
namespace AspisR1.FJe_ExternalCalls
open Aeneas Aeneas.Std Result FIq_Native
open FIv_NativeArithmetic (NQ)
abbrev Packed := Array NQ 4#usize
abbrev callback := state_only_poseidon.external_linear_packed.closure.Insts.CoreOpsFunctionFnMutTupleQM31QM31
def sum (p : Packed) : Result NQ := do
  let q0 ← Array.index_usize p 0#usize
  let s0 ← field.QM31.add field.QM31.ZERO q0
  let q1 ← Array.index_usize p 1#usize
  let s1 ← field.QM31.add s0 q1
  let q2 ← Array.index_usize p 2#usize
  let s2 ← field.QM31.add s1 q2
  let q3 ← Array.index_usize p 3#usize
  field.QM31.add s2 q3

theorem factor (s : Array NQ 16#usize) : state_only_poseidon.external_linear_packed s=
    (do
      let p ← state_only_poseidon.external_linear_packed_loop s
        (Array.repeat 4#usize field.QM31.ZERO) 0#usize
      let total ← sum p
      FIq_Native.core.array.Array.map callback p total) := by
  simp only [state_only_poseidon.external_linear_packed,sum,bind_assoc_eq]

theorem reached (s : Array NQ 16#usize) (out : Packed)
    (run : state_only_poseidon.external_linear_packed s=ok out) :
    ∃ (p : Packed) (total : NQ),
      state_only_poseidon.external_linear_packed_loop s
        (Array.repeat 4#usize field.QM31.ZERO) 0#usize=ok p ∧
      sum p=ok total ∧ FIq_Native.core.array.Array.map callback p total=ok out := by
  rw [factor] at run
  obtain ⟨p,hp,run⟩ := FIv_Map.bind_success _ _ _ run
  obtain ⟨total,ht,tail⟩ := FIv_Map.bind_success _ _ _ run
  exact ⟨p,total,hp,ht,tail⟩
#print axioms factor
#print axioms reached
end AspisR1.FJe_ExternalCalls
end
