import R1Z.PV_RunJoin_IndexedSbox19
import R1Z.PV_RunJoin_IndexedFinalSbox19
import R1Z.PV_Src_PortInternalRoundCopy
set_option autoImplicit false
namespace R1Z.PV_RunJoin_IndexedRound0919
open Aeneas Aeneas.Std Result R0Z.WriterRefine R0Z.PoseidonRefine
open BuilderForestStdPort BuilderForestAdmissionPort PV_Src_PortSboxStep
local instance : ExternalLinear := PV_Src_ExternalReference.dictionary

theorem source (s : State) (hs : Canonical s)
    (hc : poseidon2.INTERNAL.val[5]!.val < 2147483647) :
    poseidon2.apply_round_by_index s 9#usize =
      (do let out ← R0PoseidonCopy.internal_round s poseidon2.INTERNAL.val[5]! R0PoseidonCopy.INTERNAL_SHIFTS
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
  rw [if_pos (by with_unfolding_all decide)]
  try simp only [lift,bind_tc_ok,hlen]
  have hk : Array.index_usize poseidon2.INTERNAL (Usize.wrapping_sub 9#usize 4#usize) = ok poseidon2.INTERNAL.val[5]! := by
    have hsub (a b : Usize) (h : b.val ≤ a.val) : (Usize.wrapping_sub a b).val = a.val-b.val := R0Z.WriterRefine.usub a b h
    have hidx : (Usize.wrapping_sub 9#usize 4#usize) = 5#usize := by
      apply UScalar.eq_of_val_eq
      try rw [hsub _ _ (by simp)]
      try rw [hsub _ _ (by simp)]
      rfl
    rw [hidx]
    with_unfolding_all rfl
  rw [hk]
  simp only [bind_tc_ok]
  have he := congrArg (fun body : Result State => do let b ← body; ok (some (),b))
    (PV_Src_PortInternalRoundCopy.source s poseidon2.INTERNAL.val[5]! hs hc)
  simp only [PV_Src_PortInternalRoundCopy.run,bind_assoc_eq] at he
  exact he
#print axioms source
end R1Z.PV_RunJoin_IndexedRound0919
