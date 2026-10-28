import R1Z.PV_RunJoin_IndexedSbox19
set_option autoImplicit false
namespace R1Z.PV_RunJoin_IndexedInitial19
open Aeneas Aeneas.Std Result R0Z.WriterRefine R0Z.PoseidonRefine
open BuilderForestAdmissionPort PV_Src_PortSboxStep
local instance : ExternalLinear := PV_Src_ExternalReference.dictionary

theorem round0 (s : State) (hs : Canonical s)
    (hc : Canonical poseidon2.EXTERNAL_INITIAL.val[0]!) :
    poseidon2.apply_round_by_index s 0#usize =
      (do let out ← R0PoseidonCopy.full_round s poseidon2.EXTERNAL_INITIAL.val[0]!
          ok (some (),out)) := by
  rw [poseidon2.apply_round_by_index]
  simp only [lift,bind_tc_ok]
  rw [if_pos (by with_unfolding_all decide)]
  have hk : Array.index_usize poseidon2.EXTERNAL_INITIAL 0#usize = ok poseidon2.EXTERNAL_INITIAL.val[0]! := by
    with_unfolding_all rfl
  rw [hk]
  simp only [bind_tc_ok]
  rw [poseidon2.POSEIDON2_WIDTH]
  change (do
    let a ← poseidon2.apply_round_by_index_loop0 ⟨0#usize,16#usize⟩ s poseidon2.EXTERNAL_INITIAL.val[0]!
    let b ← poseidon2.external_linear_lazy a
    ok (some (),b)) = _
  rw [PV_RunJoin_IndexedSbox19.initial 16 _ (by simp) (by simp)]
  simp only [← bind_assoc_eq]
  change (do let b ← PV_Src_PortFullRoundModel.initial s poseidon2.EXTERNAL_INITIAL.val[0]!
             ok (some (),b)) = _
  rw [PV_Src_PortFullRoundCopy.initial s _ hs hc]
#print axioms round0
end R1Z.PV_RunJoin_IndexedInitial19
