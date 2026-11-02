import PV_B3P_RawTail0550227
import PV_B3P_RawReferenceFactor550227
import PV_B3P_LinkDefinitions13227
namespace PV_B3P_Association550227
open Aeneas Aeneas.Std PV_B3P_227
set_option autoImplicit false

def raw_input550 (input : Array aspis_core.field.QM31 4#usize) :
    Result (Array Limbs32_550 4#usize) :=
  from_fn_four550 (fun index => do
    let value ← Array.index_usize input index
    reference_poseidon.extension_limbs value)

def raw_source550 (input : Array aspis_core.field.QM31 4#usize) : Result Limbs64_550 := do
  let limbs ← raw_input550 input
  let a ← Array.index_usize limbs 0#usize
  let b ← Array.index_usize limbs 1#usize
  let c ← Array.index_usize limbs 2#usize
  let d ← Array.index_usize limbs 3#usize
  raw_native_tail0_550 a b c d

attribute [local irreducible] Array.index_usize reference_poseidon.extension_limbs
  reference_poseidon.raw_limb227 U64.wrapping_add U64.wrapping_sub U64.wrapping_mul
  core.convert.num.FromU64U32.from

/-- The prefix map is factored without opening any raw row or packing output. -/
theorem raw_input_continuation550 {α : Type} (input : Array aspis_core.field.QM31 4#usize)
    (next : Array Limbs32_550 4#usize → Result α) :
    (do let limbs ← raw_input550 input; next limbs) = (do
      let q0 ← Array.index_usize input 0#usize
      let a ← reference_poseidon.extension_limbs q0
      let q1 ← Array.index_usize input 1#usize
      let b ← reference_poseidon.extension_limbs q1
      let q2 ← Array.index_usize input 2#usize
      let c ← reference_poseidon.extension_limbs q2
      let q3 ← Array.index_usize input 3#usize
      let d ← reference_poseidon.extension_limbs q3
      next (Array.make 4#usize [a,b,c,d] (by simp only [List.length_cons,List.length_nil]; rfl))) := by
  simp only [raw_input550,from_fn_four550,PV_B3P_Ordered227.bind_assoc,bind_tc_ok]

/-- Only named row and suffix laws are used; raw arithmetic stays opaque. -/
theorem raw_source_reference550 (input : Array aspis_core.field.QM31 4#usize) :
    raw_source550 input = reference_poseidon.external_local_packed_raw input := by
  rw [raw_reference_factor550]
  unfold raw_source550
  rw [raw_input_continuation550]
  simp only [four_index_zero550,four_index_one550,four_index_two550,four_index_three550,bind_tc_ok]
  simp only [raw_tail0_binding550]
  rfl

theorem raw_source_link550 :
    PV_B3P_Links13227.PV_B3P_Link_poseidon_external_local_packed_raw raw_source550 :=
  funext raw_source_reference550

#print axioms raw_input_continuation550
#print axioms raw_source_reference550
#print axioms raw_source_link550
end PV_B3P_Association550227
