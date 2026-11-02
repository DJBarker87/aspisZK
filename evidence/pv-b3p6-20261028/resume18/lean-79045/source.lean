import PV_B3P_RawPack3550227
import PV_B3P_RawDebugLoops550227
import PV_B3P_FourIndex550227
namespace PV_B3P_Association550227
open Aeneas Aeneas.Std PV_B3P_227
set_option autoImplicit false

attribute [local irreducible] Array.index_usize reference_poseidon.extension_limbs
  reference_poseidon.raw_limb227 U64.wrapping_add U64.wrapping_sub U64.wrapping_mul
  core.convert.num.FromU64U32.from reference_poseidon.EXTERNAL_LOCAL_LIMB_MODULUS_BOUND

theorem raw_row_continuation550 {α : Type} (a b c d : Limbs32_550) (output : Usize)
    (next : Limbs64_550 → Result α) :
    (do let row ← raw_row550 a b c d output; next row) = (do
      let a0 ← Array.index_usize a 0#usize
      let a0w ← lift (core.convert.num.FromU64U32.from a0)
      let b0 ← Array.index_usize b 0#usize
      let b0w ← lift (core.convert.num.FromU64U32.from b0)
      let c0 ← Array.index_usize c 0#usize
      let c0w ← lift (core.convert.num.FromU64U32.from c0)
      let d0 ← Array.index_usize d 0#usize
      let d0w ← lift (core.convert.num.FromU64U32.from d0)
      let r0 ← reference_poseidon.raw_limb227 output a0w b0w c0w d0w
      let a1 ← Array.index_usize a 1#usize
      let a1w ← lift (core.convert.num.FromU64U32.from a1)
      let b1 ← Array.index_usize b 1#usize
      let b1w ← lift (core.convert.num.FromU64U32.from b1)
      let c1 ← Array.index_usize c 1#usize
      let c1w ← lift (core.convert.num.FromU64U32.from c1)
      let d1 ← Array.index_usize d 1#usize
      let d1w ← lift (core.convert.num.FromU64U32.from d1)
      let r1 ← reference_poseidon.raw_limb227 output a1w b1w c1w d1w
      let a2 ← Array.index_usize a 2#usize
      let a2w ← lift (core.convert.num.FromU64U32.from a2)
      let b2 ← Array.index_usize b 2#usize
      let b2w ← lift (core.convert.num.FromU64U32.from b2)
      let c2 ← Array.index_usize c 2#usize
      let c2w ← lift (core.convert.num.FromU64U32.from c2)
      let d2 ← Array.index_usize d 2#usize
      let d2w ← lift (core.convert.num.FromU64U32.from d2)
      let r2 ← reference_poseidon.raw_limb227 output a2w b2w c2w d2w
      let a3 ← Array.index_usize a 3#usize
      let a3w ← lift (core.convert.num.FromU64U32.from a3)
      let b3 ← Array.index_usize b 3#usize
      let b3w ← lift (core.convert.num.FromU64U32.from b3)
      let c3 ← Array.index_usize c 3#usize
      let c3w ← lift (core.convert.num.FromU64U32.from c3)
      let d3 ← Array.index_usize d 3#usize
      let d3w ← lift (core.convert.num.FromU64U32.from d3)
      let r3 ← reference_poseidon.raw_limb227 output a3w b3w c3w d3w
      next (Array.make 4#usize [r0,r1,r2,r3] (by simp only [List.length_cons,List.length_nil]; rfl))) := by
  simp only [raw_row550,from_fn_four550,raw_cell550,
    PV_B3P_Ordered227.bind_assoc,bind_tc_ok]

#print axioms raw_row_continuation550
end PV_B3P_Association550227
