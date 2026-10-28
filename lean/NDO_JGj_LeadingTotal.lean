import NDO_JGj_LeadingLoopTotal
import NDO_JGj_M31RoundTotal
import RPv_FJe_PackedValues
set_option autoImplicit false
noncomputable section
namespace AspisR1.JGj_LeadingTotal
open Aeneas Aeneas.Std Result FIq_Native
open FIw_ArrayValue (canonical decoded)
open FJa_PoseidonOrigins (Openings)
theorem source (o : Openings) (hz : canonical o.z) (hx : canonical o.xor12_z) :
    ∃ out,state_only_poseidon.leading_pair_packed o=ok out ∧ canonical out := by
  obtain ⟨absorbed,ra,ca⟩ := JGj_LeadingLoopTotal.source 8 ⟨0#usize,poseidon2.RATE⟩ o.xor12_z o.z
    (by rw [poseidon2.RATE];decide) (by rw [poseidon2.RATE];rfl) hx hz
  obtain ⟨initial,ri,ci⟩ := JGj_ExternalTotal.source absorbed ca
  obtain ⟨middle,rm,cm⟩ := JGj_M31RoundTotal.lazy initial (FJb_InitialConstants.row 0) ci (FJb_InitialConstants.bounded 0)
  obtain ⟨out,ro,co⟩ := JGj_M31RoundTotal.packed middle (FJb_InitialConstants.row 1) cm (FJb_InitialConstants.bounded 1)
  refine ⟨out,?_,co⟩
  have r0 : Array.index_usize poseidon2.EXTERNAL_INITIAL 0#usize=ok (FJb_InitialConstants.row 0) := FJb_InitialConstants.read 0#usize (by decide)
  have r1 : Array.index_usize poseidon2.EXTERNAL_INITIAL 1#usize=ok (FJb_InitialConstants.row 1) := FJb_InitialConstants.read 1#usize (by decide)
  unfold state_only_poseidon.leading_pair_packed
  rw [ra,bind_tc_ok,ri,bind_tc_ok,r0,bind_tc_ok,rm,bind_tc_ok,
    r1,bind_tc_ok,ro]
#print axioms source
end AspisR1.JGj_LeadingTotal
end
