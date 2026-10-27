import R1Z.PV_Src_PortInitialRounds
import R1Z.PV_Src_PortFinalRounds
import R1Z.PV_Src_PortInternalRounds
import R1Z.PV_Src_PortArrayTrace
import R1Z.BuilderSliceCollect

/-! Exact finite traces of the frozen 4/14/4 constant groups. Only iterator
shape and array lengths are used; no permutation is evaluated. -/
set_option autoImplicit false
namespace R1Z.PV_Src_PortConstantTraces
open Aeneas Aeneas.Std Result BuilderStdModels
open BuilderForestStdPort BuilderForestAdmissionPort PV_Src_PortSboxStep

theorem initial : FiniteTrace PV_Src_PortInitialRounds.iterator
    ⟨⟨Array.to_slice poseidon2.EXTERNAL_INITIAL,0⟩,0#usize⟩
    (PV_Src_PortEnumerateTrace.pairs poseidon2.EXTERNAL_INITIAL.val 0#usize) := by
  have ht := PV_Src_PortEnumerateTrace.trace
    (core.iter.traits.iterator.IteratorSliceIter State)
    ⟨Array.to_slice poseidon2.EXTERNAL_INITIAL,0⟩ _
    (BuilderSliceCollect.slice_trace (Array.to_slice poseidon2.EXTERNAL_INITIAL) 0)
    0#usize (by
      change 0+(poseidon2.EXTERNAL_INITIAL.val.drop 0).length ≤ 24
      simp only [List.drop_zero,Nat.zero_add]
      have h := poseidon2.EXTERNAL_INITIAL.property
      simp only [UScalar.ofNatCore_val_eq] at h
      omega)
  simpa only [PV_Src_PortInitialRounds.iterator,PV_Src_PortEnumerateTrace.iterator,
    Array.to_slice,List.drop_zero] using ht

theorem final_round : FiniteTrace PV_Src_PortFinalRounds.iterator
    ⟨⟨Array.to_slice poseidon2.EXTERNAL_FINAL,0⟩,0#usize⟩
    (PV_Src_PortEnumerateTrace.pairs poseidon2.EXTERNAL_FINAL.val 0#usize) := by
  have ht := PV_Src_PortEnumerateTrace.trace
    (core.iter.traits.iterator.IteratorSliceIter State)
    ⟨Array.to_slice poseidon2.EXTERNAL_FINAL,0⟩ _
    (BuilderSliceCollect.slice_trace (Array.to_slice poseidon2.EXTERNAL_FINAL) 0)
    0#usize (by
      change 0+(poseidon2.EXTERNAL_FINAL.val.drop 0).length ≤ 24
      simp only [List.drop_zero,Nat.zero_add]
      have h := poseidon2.EXTERNAL_FINAL.property
      simp only [UScalar.ofNatCore_val_eq] at h
      omega)
  simpa only [PV_Src_PortFinalRounds.iterator,PV_Src_PortEnumerateTrace.iterator,
    Array.to_slice,List.drop_zero] using ht

theorem internal : FiniteTrace PV_Src_PortInternalRounds.iterator
    ⟨poseidon2.INTERNAL.val,0#usize⟩
    (PV_Src_PortEnumerateTrace.pairs poseidon2.INTERNAL.val 0#usize) := by
  have ht := PV_Src_PortArrayTrace.enumerate 14#usize poseidon2.INTERNAL.val 0#usize (by
    change 0+poseidon2.INTERNAL.val.length ≤ 24
    have h := poseidon2.INTERNAL.property
    simp only [UScalar.ofNatCore_val_eq] at h
    omega)
  exact ht

#print axioms initial
#print axioms final_round
#print axioms internal
end R1Z.PV_Src_PortConstantTraces
