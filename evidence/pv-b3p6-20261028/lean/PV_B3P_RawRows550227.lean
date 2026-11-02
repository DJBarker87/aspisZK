import PV_B3P_FromFnFour550227
import PV_B3P_PoseidonCellsSuccess227
namespace PV_B3P_Association550227
open Aeneas Aeneas.Std PV_B3P_227 PV_B3P_Success227
set_option autoImplicit false

abbrev Limbs32_550 := Array U32 4#usize
abbrev Limbs64_550 := Array U64 4#usize

def raw_cell550 (a b c d : Limbs32_550) (output limb : Usize) : Result U64 := do
  let a0 ← Array.index_usize a limb
  let a1 ← lift (core.convert.num.FromU64U32.from a0)
  let b0 ← Array.index_usize b limb
  let b1 ← lift (core.convert.num.FromU64U32.from b0)
  let c0 ← Array.index_usize c limb
  let c1 ← lift (core.convert.num.FromU64U32.from c0)
  let d0 ← Array.index_usize d limb
  let d1 ← lift (core.convert.num.FromU64U32.from d0)
  reference_poseidon.raw_limb227 output a1 b1 c1 d1

def raw_row550 (a b c d : Limbs32_550) (output : Usize) : Result Limbs64_550 :=
  from_fn_four550 (raw_cell550 a b c d output)

attribute [local irreducible] U64.wrapping_add U64.wrapping_mul

theorem raw_limb_zero550 (a b c d : U64) :
    reference_poseidon.raw_limb227 0#usize a b c d =
      .ok (U64.wrapping_add (U64.wrapping_add
        (U64.wrapping_add (U64.wrapping_mul 2#u64 a) (U64.wrapping_mul 3#u64 b)) c) d) := by
  simp only [reference_poseidon.raw_limb227, lift, bind_tc_ok]

theorem raw_limb_one550 (a b c d : U64) :
    reference_poseidon.raw_limb227 1#usize a b c d =
      .ok (U64.wrapping_add (U64.wrapping_add
        (U64.wrapping_add a (U64.wrapping_mul 2#u64 b)) (U64.wrapping_mul 3#u64 c)) d) := by
  simp only [reference_poseidon.raw_limb227, lift, bind_tc_ok]

theorem raw_limb_two550 (a b c d : U64) :
    reference_poseidon.raw_limb227 2#usize a b c d =
      .ok (U64.wrapping_add (U64.wrapping_add
        (U64.wrapping_add a b) (U64.wrapping_mul 2#u64 c)) (U64.wrapping_mul 3#u64 d)) := by
  simp only [reference_poseidon.raw_limb227, lift, bind_tc_ok]

theorem raw_limb_three550 (a b c d : U64) :
    reference_poseidon.raw_limb227 3#usize a b c d =
      .ok (U64.wrapping_add (U64.wrapping_add
        (U64.wrapping_add (U64.wrapping_mul 3#u64 a) b) c) (U64.wrapping_mul 2#u64 d)) := by
  simp only [reference_poseidon.raw_limb227, lift, bind_tc_ok]

theorem raw_cell_total550 (a b c d : Limbs32_550) (output limb : Usize)
    (ho : output.val < 4) (hl : limb.val < 4) :
    Success (raw_cell550 a b c d output limb) := by
  unfold raw_cell550
  apply bind _ _ (index a limb hl)
  intro a0
  simp only [lift, bind_tc_ok]
  apply bind _ _ (index b limb hl)
  intro b0
  simp only [lift, bind_tc_ok]
  apply bind _ _ (index c limb hl)
  intro c0
  simp only [lift, bind_tc_ok]
  apply bind _ _ (index d limb hl)
  intro d0
  simp only [lift, bind_tc_ok]
  exact raw_limb_total _ _ _ _ _ ho

theorem raw_row_total550 (a b c d : Limbs32_550) (output : Usize)
    (ho : output.val < 4) : Success (raw_row550 a b c d output) :=
  from_fn_four_total550 _ (fun limb hl => raw_cell_total550 a b c d output limb ho hl)

#print axioms raw_limb_zero550
#print axioms raw_limb_one550
#print axioms raw_limb_two550
#print axioms raw_limb_three550
#print axioms raw_cell_total550
#print axioms raw_row_total550
end PV_B3P_Association550227
