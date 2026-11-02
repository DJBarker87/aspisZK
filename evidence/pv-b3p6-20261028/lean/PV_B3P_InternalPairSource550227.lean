import PV_B3P_ArrayInterface543227
import PV_B3P_Ordered227
import PV_B3P_P227_06
import PV_B3P_LinkDefinitions13227
namespace PV_B3P_Association550227
open Aeneas Aeneas.Std PV_B3P_227
set_option autoImplicit false

/-- The fixed ROWS.map constructor, preserving callback order and failure. -/
def rows_map550 {α : Type} (f : Usize → Result α) : Result (Array α 7#usize) := do
  let a ← f 2#usize
  let b ← f 3#usize
  let c ← f 4#usize
  let d ← f 5#usize
  let e ← f 6#usize
  let g ← f 7#usize
  let h ← f 8#usize
  .ok (Array.make 7#usize [a,b,c,d,e,g,h] (by simp only [List.length_cons,List.length_nil]; rfl))

def even_row550 (row : Usize) : Result U32 := do
  let offset ← lift (Usize.wrapping_sub row 2#usize)
  let index ← lift (Usize.wrapping_mul 2#usize offset)
  Array.index_usize reference_poseidon.INTERNAL index

def odd_row550 (row : Usize) : Result U32 := do
  let offset ← lift (Usize.wrapping_sub row 2#usize)
  let index ← lift (Usize.wrapping_mul 2#usize offset)
  let index1 ← lift (Usize.wrapping_add index 1#usize)
  Array.index_usize reference_poseidon.INTERNAL index1

def internal_pair_source550 (state local1 : Array aspis_core.field.QM31 16#usize) :
    Result (Array aspis_core.field.QM31 16#usize) := do
  let weights ← rows_map550 (Array.index_usize local1)
  let evenConstants ← rows_map550 even_row550
  let oddConstants ← rows_map550 odd_row550
  let even ← reference_field.qm31_m31_dot weights evenConstants
  let odd ← reference_field.qm31_m31_dot weights oddConstants
  let next ← reference_poseidon.internal_round state even
  reference_poseidon.internal_round next odd

attribute [local irreducible] Array.index_usize reference_field.qm31_m31_dot
  reference_poseidon.internal_round Usize.wrapping_sub Usize.wrapping_mul Usize.wrapping_add

theorem internal_pair_reference550 (state local1 : Array aspis_core.field.QM31 16#usize) :
    internal_pair_source550 state local1 =
      reference_poseidon.interpolated_internal_pair state local1 := by
  simp only [internal_pair_source550, rows_map550, even_row550, odd_row550,
    reference_poseidon.interpolated_internal_pair, PV_B3P_Ordered227.bind_assoc]
  rfl

theorem internal_pair_source_link550 :
    PV_B3P_Links13227.PV_B3P_Link_poseidon_interpolated_internal_pair internal_pair_source550 :=
  funext fun state => funext (internal_pair_reference550 state)

#print axioms internal_pair_reference550
#print axioms internal_pair_source_link550
end PV_B3P_Association550227
