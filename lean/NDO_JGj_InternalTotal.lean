import NDO_JGj_InternalPrepare
import NDO_JGj_InternalLaneLoop
set_option autoImplicit false
noncomputable section
namespace AspisR1.JGj_InternalTotal
open Aeneas Aeneas.Std Result FIq_Native
open FJb_MatrixGroupStep (State)
theorem factor (s : State) : state_only_poseidon.internal_linear_lazy s=(do
    let (s1,full) ← JGj_InternalPrepare.source s
    state_only_poseidon.internal_linear_lazy_loop1 ⟨1#usize,poseidon2.POSEIDON2_WIDTH⟩ s1 full) := by
  simp only [state_only_poseidon.internal_linear_lazy,JGj_InternalPrepare.source,bind_assoc_eq,bind_tc_ok,
    JGj_InternalFullSum.Full,JGj_InternalZeroEquation.Callback]
  rfl
theorem source (s : State) (hs : FIw_ArrayValue.canonical s) :
    ∃ out,state_only_poseidon.internal_linear_lazy s=ok out ∧ FIw_ArrayValue.canonical out := by
  obtain ⟨s1,full,rp,cs,bf⟩ := JGj_InternalPrepare.success s hs
  obtain ⟨out,ro,co⟩ := JGj_InternalLaneLoop.source 15 ⟨1#usize,poseidon2.POSEIDON2_WIDTH⟩ s1 full
    (by decide) (by rw [poseidon2.POSEIDON2_WIDTH];decide) (by rw [poseidon2.POSEIDON2_WIDTH];rfl) bf cs
  refine ⟨out,?_,co⟩
  rw [factor,rp,bind_tc_ok]
  exact ro
#print axioms factor
#print axioms source
end AspisR1.JGj_InternalTotal
end
