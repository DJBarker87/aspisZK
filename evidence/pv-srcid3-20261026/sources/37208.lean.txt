import R1Z.PV_Src_PortField
import R1Z.BuilderBankRange
import R1Z.BuilderRecordsArray

/-! One symbolic nonlinear cell of each actual external-round loop. The
remaining loop Result is retained exactly; no permutation is evaluated. -/
set_option autoImplicit false
namespace R1Z.PV_Src_PortSboxStep
open Aeneas Aeneas.Std Result R0Z.WriterRefine
open BuilderForestAdmissionPort
abbrev State := Array U32 16#usize

def Canonical (state : State) : Prop :=
  ∀ j : Fin 16, (state.val[j.val]!).val < 2147483647

theorem canonical_set (state : State) (index : Usize) (hi : index.val < 16)
    (x : U32) (hx : x.val < 2147483647) (hc : Canonical state) :
    Canonical (state.set index x) := by
  intro j
  rw [BuilderRecordsArray.set_get state index x j.val (by simpa using hi)]
  split
  · exact hx
  · exact hc j

variable {K : Type} [Field K] [CharP K 2147483647]

theorem initial_step (iter after : core.ops.range.Range Usize)
    (state constants1 : State) (index : Usize) (hi : index.val < 16)
    (next : core.iter.range.IteratorRange.next core.iter.range.StepUsize iter =
      ok (some index,after)) (hs : Canonical state) (hc : Canonical constants1) :
    ∃ x, poseidon2.permute_optimized_with_trace_loop0_loop0 iter state constants1 =
      poseidon2.permute_optimized_with_trace_loop0_loop0 after (state.set index x) constants1 ∧
      x.val < 2147483647 ∧ liftU (K := K) x =
        R0P.poseidonPow5 (liftU state.val[index.val]! + liftU constants1.val[index.val]!) := by
  obtain ⟨sum,hadd,_,haddv⟩ := PV_Src_PortField.addition (K := K)
    state.val[index.val]! constants1.val[index.val]! (hs ⟨index.val,hi⟩) (hc ⟨index.val,hi⟩)
  obtain ⟨x,hpow,hcan,hpowv⟩ := PV_Src_PortField.power (K := K) sum
  refine ⟨x,?_,hcan,by rw [hpowv,haddv]⟩
  rw [poseidon2.permute_optimized_with_trace_loop0_loop0,next]
  simp only [bind_tc_ok]
  rw [index_ok state index (by simpa using hi)]
  simp only [bind_tc_ok]
  rw [index_ok constants1 index (by simpa using hi)]
  simp only [bind_tc_ok]
  rw [hadd]
  simp only [bind_tc_ok]
  rw [hpow]
  simp only [bind_tc_ok]
  rw [BuilderRecordsArray.update_gen _ index _ (by simpa using hi)]
  rfl

theorem final_step (iter after : core.ops.range.Range Usize)
    (state constants1 : State) (index : Usize) (hi : index.val < 16)
    (next : core.iter.range.IteratorRange.next core.iter.range.StepUsize iter =
      ok (some index,after)) (hs : Canonical state) (hc : Canonical constants1) :
    ∃ x, poseidon2.permute_optimized_with_trace_loop2_loop0 iter state constants1 =
      poseidon2.permute_optimized_with_trace_loop2_loop0 after (state.set index x) constants1 ∧
      x.val < 2147483647 ∧ liftU (K := K) x =
        R0P.poseidonPow5 (liftU state.val[index.val]! + liftU constants1.val[index.val]!) := by
  obtain ⟨sum,hadd,_,haddv⟩ := PV_Src_PortField.addition (K := K)
    state.val[index.val]! constants1.val[index.val]! (hs ⟨index.val,hi⟩) (hc ⟨index.val,hi⟩)
  obtain ⟨x,hpow,hcan,hpowv⟩ := PV_Src_PortField.power (K := K) sum
  refine ⟨x,?_,hcan,by rw [hpowv,haddv]⟩
  rw [poseidon2.permute_optimized_with_trace_loop2_loop0,next]
  simp only [bind_tc_ok]
  rw [index_ok state index (by simpa using hi)]
  simp only [bind_tc_ok]
  rw [index_ok constants1 index (by simpa using hi)]
  simp only [bind_tc_ok]
  rw [hadd]
  simp only [bind_tc_ok]
  rw [hpow]
  simp only [bind_tc_ok]
  rw [BuilderRecordsArray.update_gen _ index _ (by simpa using hi)]
  rfl

#print axioms canonical_set
#print axioms initial_step
#print axioms final_step
end R1Z.PV_Src_PortSboxStep
