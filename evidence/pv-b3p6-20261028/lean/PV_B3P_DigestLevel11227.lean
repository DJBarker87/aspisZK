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
  let shift ← lift (UScalar.cast .U32 level)
  let shifted ← lift (U64.wrapping_shr public1.transition.live_snapshot.next_pair_index shift)
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

theorem digest_shift11_0 : UScalar.cast .U32 0#usize = 0#u32 := Eq.refl _
#print axioms digest_shift11_0
theorem digest_shift11_1 : UScalar.cast .U32 1#usize = 1#u32 := Eq.refl _
#print axioms digest_shift11_1
theorem digest_shift11_2 : UScalar.cast .U32 2#usize = 2#u32 := Eq.refl _
#print axioms digest_shift11_2
theorem digest_shift11_3 : UScalar.cast .U32 3#usize = 3#u32 := Eq.refl _
#print axioms digest_shift11_3
theorem digest_shift11_4 : UScalar.cast .U32 4#usize = 4#u32 := Eq.refl _
#print axioms digest_shift11_4
theorem digest_shift11_5 : UScalar.cast .U32 5#usize = 5#u32 := Eq.refl _
#print axioms digest_shift11_5
theorem digest_shift11_6 : UScalar.cast .U32 6#usize = 6#u32 := Eq.refl _
#print axioms digest_shift11_6
theorem digest_shift11_7 : UScalar.cast .U32 7#usize = 7#u32 := Eq.refl _
#print axioms digest_shift11_7
theorem digest_shift11_8 : UScalar.cast .U32 8#usize = 8#u32 := Eq.refl _
#print axioms digest_shift11_8
theorem digest_shift11_9 : UScalar.cast .U32 9#usize = 9#u32 := Eq.refl _
#print axioms digest_shift11_9
theorem digest_shift11_10 : UScalar.cast .U32 10#usize = 10#u32 := Eq.refl _
#print axioms digest_shift11_10
theorem digest_shift11_11 : UScalar.cast .U32 11#usize = 11#u32 := Eq.refl _
#print axioms digest_shift11_11
theorem digest_shift11_12 : UScalar.cast .U32 12#usize = 12#u32 := Eq.refl _
#print axioms digest_shift11_12
theorem digest_shift11_13 : UScalar.cast .U32 13#usize = 13#u32 := Eq.refl _
#print axioms digest_shift11_13
theorem digest_shift11_14 : UScalar.cast .U32 14#usize = 14#u32 := Eq.refl _
#print axioms digest_shift11_14
theorem digest_shift11_15 : UScalar.cast .U32 15#usize = 15#u32 := Eq.refl _
#print axioms digest_shift11_15
theorem digest_shift11_16 : UScalar.cast .U32 16#usize = 16#u32 := Eq.refl _
#print axioms digest_shift11_16
theorem digest_shift11_17 : UScalar.cast .U32 17#usize = 17#u32 := Eq.refl _
#print axioms digest_shift11_17
theorem digest_shift11_18 : UScalar.cast .U32 18#usize = 18#u32 := Eq.refl _
#print axioms digest_shift11_18
theorem digest_shift11_19 : UScalar.cast .U32 19#usize = 19#u32 := Eq.refl _
#print axioms digest_shift11_19
end PV_B3P_Binding11227
