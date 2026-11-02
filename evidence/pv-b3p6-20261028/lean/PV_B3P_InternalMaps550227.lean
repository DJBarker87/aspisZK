import PV_B3P_ArrayInterface543227
import PV_B3P_Ordered227
import PV_B3P_P227_06
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


attribute [local irreducible] Array.index_usize reference_field.qm31_m31_dot
  reference_poseidon.internal_round Usize.wrapping_sub Usize.wrapping_mul Usize.wrapping_add

theorem weights_continuation550 {α : Type} (local1 : Array aspis_core.field.QM31 16#usize)
    (next : Array aspis_core.field.QM31 7#usize → Result α) :
    (do let values ← rows_map550 (Array.index_usize local1); next values) = (do
      let v0 ← Array.index_usize local1 2#usize
      let v1 ← Array.index_usize local1 3#usize
      let v2 ← Array.index_usize local1 4#usize
      let v3 ← Array.index_usize local1 5#usize
      let v4 ← Array.index_usize local1 6#usize
      let v5 ← Array.index_usize local1 7#usize
      let v6 ← Array.index_usize local1 8#usize
      next (Array.make 7#usize [v0,v1,v2,v3,v4,v5,v6] (by simp only [List.length_cons,List.length_nil]; rfl))) := by
  simp only [rows_map550,
    PV_B3P_Ordered227.bind_assoc,bind_tc_ok]

#print axioms weights_continuation550

theorem even_continuation550 {α : Type} 
    (next : Array U32 7#usize → Result α) :
    (do let values ← rows_map550 even_row550; next values) = (do
      let offset0 ← lift (Usize.wrapping_sub 2#usize 2#usize)
      let index0 ← lift (Usize.wrapping_mul 2#usize offset0)
      let v0 ← Array.index_usize reference_poseidon.INTERNAL index0
      let offset1 ← lift (Usize.wrapping_sub 3#usize 2#usize)
      let index1 ← lift (Usize.wrapping_mul 2#usize offset1)
      let v1 ← Array.index_usize reference_poseidon.INTERNAL index1
      let offset2 ← lift (Usize.wrapping_sub 4#usize 2#usize)
      let index2 ← lift (Usize.wrapping_mul 2#usize offset2)
      let v2 ← Array.index_usize reference_poseidon.INTERNAL index2
      let offset3 ← lift (Usize.wrapping_sub 5#usize 2#usize)
      let index3 ← lift (Usize.wrapping_mul 2#usize offset3)
      let v3 ← Array.index_usize reference_poseidon.INTERNAL index3
      let offset4 ← lift (Usize.wrapping_sub 6#usize 2#usize)
      let index4 ← lift (Usize.wrapping_mul 2#usize offset4)
      let v4 ← Array.index_usize reference_poseidon.INTERNAL index4
      let offset5 ← lift (Usize.wrapping_sub 7#usize 2#usize)
      let index5 ← lift (Usize.wrapping_mul 2#usize offset5)
      let v5 ← Array.index_usize reference_poseidon.INTERNAL index5
      let offset6 ← lift (Usize.wrapping_sub 8#usize 2#usize)
      let index6 ← lift (Usize.wrapping_mul 2#usize offset6)
      let v6 ← Array.index_usize reference_poseidon.INTERNAL index6
      next (Array.make 7#usize [v0,v1,v2,v3,v4,v5,v6] (by simp only [List.length_cons,List.length_nil]; rfl))) := by
  simp only [rows_map550,even_row550,
    PV_B3P_Ordered227.bind_assoc,bind_tc_ok]

#print axioms even_continuation550

theorem odd_continuation550 {α : Type} 
    (next : Array U32 7#usize → Result α) :
    (do let values ← rows_map550 odd_row550; next values) = (do
      let offset0 ← lift (Usize.wrapping_sub 2#usize 2#usize)
      let index0 ← lift (Usize.wrapping_mul 2#usize offset0)
      let next0 ← lift (Usize.wrapping_add index0 1#usize)
      let v0 ← Array.index_usize reference_poseidon.INTERNAL next0
      let offset1 ← lift (Usize.wrapping_sub 3#usize 2#usize)
      let index1 ← lift (Usize.wrapping_mul 2#usize offset1)
      let next1 ← lift (Usize.wrapping_add index1 1#usize)
      let v1 ← Array.index_usize reference_poseidon.INTERNAL next1
      let offset2 ← lift (Usize.wrapping_sub 4#usize 2#usize)
      let index2 ← lift (Usize.wrapping_mul 2#usize offset2)
      let next2 ← lift (Usize.wrapping_add index2 1#usize)
      let v2 ← Array.index_usize reference_poseidon.INTERNAL next2
      let offset3 ← lift (Usize.wrapping_sub 5#usize 2#usize)
      let index3 ← lift (Usize.wrapping_mul 2#usize offset3)
      let next3 ← lift (Usize.wrapping_add index3 1#usize)
      let v3 ← Array.index_usize reference_poseidon.INTERNAL next3
      let offset4 ← lift (Usize.wrapping_sub 6#usize 2#usize)
      let index4 ← lift (Usize.wrapping_mul 2#usize offset4)
      let next4 ← lift (Usize.wrapping_add index4 1#usize)
      let v4 ← Array.index_usize reference_poseidon.INTERNAL next4
      let offset5 ← lift (Usize.wrapping_sub 7#usize 2#usize)
      let index5 ← lift (Usize.wrapping_mul 2#usize offset5)
      let next5 ← lift (Usize.wrapping_add index5 1#usize)
      let v5 ← Array.index_usize reference_poseidon.INTERNAL next5
      let offset6 ← lift (Usize.wrapping_sub 8#usize 2#usize)
      let index6 ← lift (Usize.wrapping_mul 2#usize offset6)
      let next6 ← lift (Usize.wrapping_add index6 1#usize)
      let v6 ← Array.index_usize reference_poseidon.INTERNAL next6
      next (Array.make 7#usize [v0,v1,v2,v3,v4,v5,v6] (by simp only [List.length_cons,List.length_nil]; rfl))) := by
  simp only [rows_map550,odd_row550,
    PV_B3P_Ordered227.bind_assoc,bind_tc_ok]

#print axioms odd_continuation550

end PV_B3P_Association550227
