import R1Z.PV_Src_ExternalLanes

set_option autoImplicit false
namespace R1Z.PV_Src_ExternalTotal
open Aeneas Aeneas.Std Result
open AspisBuilderPoseidonReference

theorem total (state : Array U32 16#usize) : ∃ out, PV_Src_ExternalReference.run state = ok out := by
  obtain ⟨blocks,hb⟩ := PV_Src_ExternalBlocks.total state 0#usize (by simp)
  obtain ⟨sums,hs⟩ := PV_Src_ExternalSums.total blocks (Array.repeat 4#usize 0#u64) 0#usize (by simp)
  obtain ⟨out,ho⟩ := PV_Src_ExternalLanes.total blocks sums 0#usize (by simp)
  refine ⟨out,?_⟩
  rw [PV_Src_ExternalReference.run,poseidon2.builder_reference.external_owned,hb]
  simp only [bind_tc_ok]
  rw [hs]
  simpa only [bind_tc_ok] using ho

#print axioms total
end R1Z.PV_Src_ExternalTotal
