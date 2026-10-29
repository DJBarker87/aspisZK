import PV_B3P_DigestRead904227
import PV_B3P_Ordered227
namespace PV_B3P_Binding11227
open Aeneas Aeneas.Std PV_B3P_227 PV_B3P_Binding9227 PV_B3P_Success227
set_option autoImplicit false

/-- One source level: identical order of selector read, root/frontier read, and digest update. -/
def digest_level11 (public1 : reference_terminal.SemanticPublic)
    (openings : aspis_statement.state_only_poseidon.StateOnlyPoseidonOpenings)
    (selectors : reference_copy_terminal.Selectors) (output : Digest8Q)
    (level : Usize) : Result Digest8Q := do
  let block ← lift (Usize.wrapping_add 34#usize level)
  let shifted ← lift (U64.wrapping_shr public1.transition.live_snapshot.next_pair_index level)
  let bit ← lift (shifted &&& 1#u64)
  if bit = 0#u64 then
    let row ← lift (Usize.wrapping_mul block 16#usize)
    let selector ← reference_copy_terminal.Selectors.row selectors row
    let root ← reference_terminal.empty_root level
    reference_terminal.add_digest_binding output selector openings.z aspis_statement.poseidon2.RATE root true
  else
    let row ← lift (Usize.wrapping_mul block 16#usize)
    let row1 ← lift (Usize.wrapping_add row 12#usize)
    let selector ← reference_copy_terminal.Selectors.row selectors row1
    let frontier ← Array.index_usize public1.transition.live_snapshot.frontier level
    reference_terminal.add_digest_binding output selector openings.z 0#usize frontier false

theorem digest_shift11_0 (index : U64) : U64.wrapping_shr index 0#u32 = U64.wrapping_shr index 0#usize := Eq.refl _
#print axioms digest_shift11_0
theorem digest_shift11_1 (index : U64) : U64.wrapping_shr index 1#u32 = U64.wrapping_shr index 1#usize := Eq.refl _
#print axioms digest_shift11_1
theorem digest_shift11_2 (index : U64) : U64.wrapping_shr index 2#u32 = U64.wrapping_shr index 2#usize := Eq.refl _
#print axioms digest_shift11_2
theorem digest_shift11_3 (index : U64) : U64.wrapping_shr index 3#u32 = U64.wrapping_shr index 3#usize := Eq.refl _
#print axioms digest_shift11_3
theorem digest_shift11_4 (index : U64) : U64.wrapping_shr index 4#u32 = U64.wrapping_shr index 4#usize := Eq.refl _
#print axioms digest_shift11_4
theorem digest_shift11_5 (index : U64) : U64.wrapping_shr index 5#u32 = U64.wrapping_shr index 5#usize := Eq.refl _
#print axioms digest_shift11_5
theorem digest_shift11_6 (index : U64) : U64.wrapping_shr index 6#u32 = U64.wrapping_shr index 6#usize := Eq.refl _
#print axioms digest_shift11_6
theorem digest_shift11_7 (index : U64) : U64.wrapping_shr index 7#u32 = U64.wrapping_shr index 7#usize := Eq.refl _
#print axioms digest_shift11_7
theorem digest_shift11_8 (index : U64) : U64.wrapping_shr index 8#u32 = U64.wrapping_shr index 8#usize := Eq.refl _
#print axioms digest_shift11_8
theorem digest_shift11_9 (index : U64) : U64.wrapping_shr index 9#u32 = U64.wrapping_shr index 9#usize := Eq.refl _
#print axioms digest_shift11_9
theorem digest_shift11_10 (index : U64) : U64.wrapping_shr index 10#u32 = U64.wrapping_shr index 10#usize := Eq.refl _
#print axioms digest_shift11_10
theorem digest_shift11_11 (index : U64) : U64.wrapping_shr index 11#u32 = U64.wrapping_shr index 11#usize := Eq.refl _
#print axioms digest_shift11_11
theorem digest_shift11_12 (index : U64) : U64.wrapping_shr index 12#u32 = U64.wrapping_shr index 12#usize := Eq.refl _
#print axioms digest_shift11_12
theorem digest_shift11_13 (index : U64) : U64.wrapping_shr index 13#u32 = U64.wrapping_shr index 13#usize := Eq.refl _
#print axioms digest_shift11_13
theorem digest_shift11_14 (index : U64) : U64.wrapping_shr index 14#u32 = U64.wrapping_shr index 14#usize := Eq.refl _
#print axioms digest_shift11_14
theorem digest_shift11_15 (index : U64) : U64.wrapping_shr index 15#u32 = U64.wrapping_shr index 15#usize := Eq.refl _
#print axioms digest_shift11_15
theorem digest_shift11_16 (index : U64) : U64.wrapping_shr index 16#u32 = U64.wrapping_shr index 16#usize := Eq.refl _
#print axioms digest_shift11_16
theorem digest_shift11_17 (index : U64) : U64.wrapping_shr index 17#u32 = U64.wrapping_shr index 17#usize := Eq.refl _
#print axioms digest_shift11_17
theorem digest_shift11_18 (index : U64) : U64.wrapping_shr index 18#u32 = U64.wrapping_shr index 18#usize := Eq.refl _
#print axioms digest_shift11_18
theorem digest_shift11_19 (index : U64) : U64.wrapping_shr index 19#u32 = U64.wrapping_shr index 19#usize := Eq.refl _
#print axioms digest_shift11_19
end PV_B3P_Binding11227
