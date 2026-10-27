import R1Z.PV_RunJoin_IndexedSbox19
import R1Z.PV_RunJoin_IndexedFinalSbox19
import R1Z.PV_Src_PortInternalRoundCopy
set_option autoImplicit false
namespace R1Z.PV_RunJoin_IndexedRound1819
open Aeneas Aeneas.Std Result R0Z.WriterRefine R0Z.PoseidonRefine
open BuilderForestStdPort BuilderForestAdmissionPort PV_Src_PortSboxStep
local instance : ExternalLinear := PV_Src_ExternalReference.dictionary

theorem source (s : State) (hs : Canonical s)
    (hc : Canonical poseidon2.EXTERNAL_FINAL.val[0]!) :
    poseidon2.apply_round_by_index s 18#usize =
      (do let out ← R0PoseidonCopy.full_round s poseidon2.EXTERNAL_FINAL.val[0]!
          ok (some (),out)) := by
  have hlen {α : Type} {n : Usize} (a : Array α n) : Slice.len (Array.to_slice a) = n := by
    apply UScalar.eq_of_val_eq
    simp only [Slice.len_val,Array.length_to_slice]
  rw [poseidon2.apply_round_by_index]
  simp only [hlen]
  try simp only [lift,bind_tc_ok,hlen]
  rw [if_neg (by with_unfolding_all scalar_tac)]
  try simp only [lift,bind_tc_ok,hlen]
  have hadd : Usize.wrapping_add 4#usize 14#usize = 18#usize := by
    apply UScalar.eq_of_val_eq
    rw [uadd _ _ (by simp)]
    rfl
  rw [hadd]
  rw [if_neg (by with_unfolding_all decide)]
  rw [if_pos (by with_unfolding_all decide)]
  try simp only [lift,bind_tc_ok,hlen]
  have hinner : Usize.wrapping_sub 18#usize 4#usize = 14#usize := by
    apply UScalar.eq_of_val_eq
    rw [R0Z.WriterRefine.usub _ _ (by simp)]
    rfl
  rw [hinner]
  have hk : Array.index_usize poseidon2.EXTERNAL_FINAL (Usize.wrapping_sub 14#usize 14#usize) = ok poseidon2.EXTERNAL_FINAL.val[0]! := by
    have hsub (a b : Usize) (h : b.val ≤ a.val) : (Usize.wrapping_sub a b).val = a.val-b.val := R0Z.WriterRefine.usub a b h
    have hidx : (Usize.wrapping_sub 14#usize 14#usize) = 0#usize := by
      apply UScalar.eq_of_val_eq
      try rw [hsub _ _ (by simp)]
      try rw [hsub _ _ (by simp)]
      rfl
    rw [hidx]
    with_unfolding_all rfl
  rw [hk]
  simp only [bind_tc_ok]
  rw [poseidon2.POSEIDON2_WIDTH]
  rw [PV_RunJoin_IndexedFinalSbox19.final_round 16 _ (by simp) (by simp)]
  simp only [← bind_assoc_eq]
  change (do let b ← PV_Src_PortFullRoundModel.final_round s poseidon2.EXTERNAL_FINAL.val[0]!
             ok (some (),b)) = _
  rw [PV_Src_PortFullRoundCopy.final_round s _ hs hc]
#print axioms source
end R1Z.PV_RunJoin_IndexedRound1819
