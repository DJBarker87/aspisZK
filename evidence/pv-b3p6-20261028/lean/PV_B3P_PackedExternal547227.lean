import PV_B3P_ArrayInterface543227
import PV_B3P_RangeFold13227
import PV_B3P_P227_04
import PV_B3P_LinkDefinitions13227
namespace PV_B3P_Association547227
open Aeneas Aeneas.Std PV_B3P_227 PV_B3P_Binding9227 PV_B3P_Binding11227 PV_B3P_Binding13227
set_option autoImplicit false

def packed_group_step547 (state : Array aspis_core.field.QM31 16#usize)
    (localPacked : Array aspis_core.field.QM31 4#usize) (group : Usize) :
    Result (Array aspis_core.field.QM31 4#usize) := do
  let start ← lift (Std.Usize.wrapping_mul 4#usize group)
  let a ← Array.index_usize state start
  let i1 ← lift (Std.Usize.wrapping_add start 1#usize)
  let b ← Array.index_usize state i1
  let i2 ← lift (Std.Usize.wrapping_add start 2#usize)
  let c ← Array.index_usize state i2
  let i3 ← lift (Std.Usize.wrapping_add start 3#usize)
  let d ← Array.index_usize state i3
  let value ← reference_poseidon.external_local_packed
    (Array.make 4#usize [a,b,c,d] (by simp only [List.length_cons,List.length_nil]; rfl))
  Array.update localPacked group value

def packed_finish547 (localPacked : Array aspis_core.field.QM31 4#usize) :
    Result (Array aspis_core.field.QM31 4#usize) := do
  let a ← Array.index_usize localPacked 0#usize
  let s0 ← aspis_core.field.QM31.add aspis_core.field.QM31.ZERO a
  let b ← Array.index_usize localPacked 1#usize
  let s1 ← aspis_core.field.QM31.add s0 b
  let c ← Array.index_usize localPacked 2#usize
  let s2 ← aspis_core.field.QM31.add s1 c
  let d ← Array.index_usize localPacked 3#usize
  let sum ← aspis_core.field.QM31.add s2 d
  let x0 ← aspis_core.field.QM31.add a sum
  let x1 ← aspis_core.field.QM31.add b sum
  let x2 ← aspis_core.field.QM31.add c sum
  let x3 ← aspis_core.field.QM31.add d sum
  .ok (Array.make 4#usize [x0,x1,x2,x3] (by simp only [List.length_cons,List.length_nil]; rfl))

def source_external_packed547 (state : Array aspis_core.field.QM31 16#usize) :
    Result (Array aspis_core.field.QM31 4#usize) := do
  let localPacked ← range_loop13 (packed_group_step547 state) 0#usize 4#usize
    (Array.repeat 4#usize aspis_core.field.QM31.ZERO)
  packed_finish547 localPacked

attribute [local irreducible] Array.index_usize Array.update reference_poseidon.external_local_packed aspis_core.field.QM31.add

theorem four_group_indices547 : usize_indices11 4 0#usize =
    [0#usize,1#usize,2#usize,3#usize] := by
  simp only [usize_indices11,next11_20_0,next11_20_1,next11_20_2,next11_20_3]

theorem external_packed_reference547 (state : Array aspis_core.field.QM31 16#usize) :
    source_external_packed547 state = reference_poseidon.external_linear_packed state := by
  unfold source_external_packed547
  rw [range_as_fold13 _ 0#usize 4#usize 4 _ (by rfl),four_group_indices547]
  simp only [PV_B3P_Ordered227.fold,packed_group_step547,packed_finish547,
    reference_poseidon.external_linear_packed,PV_B3P_Ordered227.bind_assoc]
  rfl

theorem external_packed_source_link547 :
    PV_B3P_Links13227.PV_B3P_Link_poseidon_external_linear_packed source_external_packed547 :=
  funext external_packed_reference547

#print axioms four_group_indices547
#print axioms external_packed_reference547
#print axioms external_packed_source_link547
end PV_B3P_Association547227
