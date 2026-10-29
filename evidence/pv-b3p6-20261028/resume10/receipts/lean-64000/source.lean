import PV_B3P_ValueRead914227
import PV_B3P_DigestCpsEq9227
namespace PV_B3P_Binding10227
open Aeneas Aeneas.Std PV_B3P_227 PV_B3P_Binding9227 Result ControlFlow Error
set_option autoImplicit false

def value_source_tail10_14 (packed : Array aspis_core.field.QM31 24#usize)
    (openings : aspis_statement.state_only_poseidon.StateOnlyPoseidonOpenings)
    (selectors : reference_copy_terminal.Selectors) (state : ValueState9) : Result (Array aspis_core.field.QM31 24#usize) := do
  let packed1 ← reference_terminal.add_preweighted packed 49#usize state.2
  let i27 ←
    lift (Std.Usize.wrapping_mul 16#usize
      reference_terminal.VALUE_AUXILIARY_BLOCK)
  let i28 ← lift (Std.Usize.wrapping_add i27 6#usize)
  let conservation_selector ←
    reference_copy_terminal.Selectors.row selectors i28
  let q174 ← Array.index_usize openings.z 0#usize
  let q175 ← Array.index_usize openings.z 1#usize
  let q176 ← aspis_core.field.QM31.sub q174 q175
  let q177 ← Array.index_usize openings.z 2#usize
  let q178 ← aspis_core.field.QM31.sub q176 q177
  let q179 ← aspis_core.field.QM31.mul conservation_selector q178
  let q180 ← Array.index_usize openings.succ_z 0#usize
  let q181 ← Array.index_usize openings.succ_z 1#usize
  let q182 ← aspis_core.field.QM31.sub q180 q181
  let q183 ← aspis_core.field.QM31.mul conservation_selector q182
  reference_terminal.add_preweighted packed1 82#usize
    (Array.make 2#usize [ q179, q183 ] (by simp only [List.length_cons,List.length_nil]; rfl))

/-- [pv_b3p6_reference227::reference_terminal::variant_expected_output]:
    Source: 'reference_terminal.rs', lines 979:0-984:1 -/
def reference_terminal.variant_expected_output
  (variant : reference_terminal.CompiledVariant) :
  Result aspis_core.field.M31
  := do
  match variant with
  | reference_terminal.CompiledVariant.PrivateTransfer => ok 1#u32
  | reference_terminal.CompiledVariant.Withdrawal => ok 0#u32

/-- [pv_b3p6_reference227::reference_terminal::occupancy_lanes_literal]:
    Source: 'reference_terminal.rs', lines 1014:0-1056:1 -/
def reference_terminal.occupancy_lanes_literal
  (input_occupancy : aspis_core.field.QM31)
  (output_occupancy : aspis_core.field.QM31)
  (expected_output : aspis_core.field.M31)
  (opened : Array aspis_core.field.QM31 16#usize) :
  Result (Array aspis_core.field.QM31 12#usize)
  := do
  let occupied ← Array.index_usize opened 0#usize
  let inverse ← Array.index_usize opened 1#usize
  let one_minus ←
    aspis_core.field.QM31.sub aspis_core.field.QM31.ONE occupied
  let occupancy := Array.repeat 12#usize aspis_core.field.QM31.ZERO
  let both ← aspis_core.field.QM31.add input_occupancy output_occupancy
  let q ← aspis_core.field.QM31.sub occupied aspis_core.field.QM31.ONE
  let q1 ← aspis_core.field.QM31.mul occupied q
  let q2 ← aspis_core.field.QM31.mul both q1
  let occupancy1 ← Array.update occupancy 0#usize q2
  let q3 ← Array.index_usize opened 9#usize
  let q4 ← aspis_core.field.QM31.mul q3 inverse
  let q5 ← aspis_core.field.QM31.sub q4 occupied
  let q6 ← aspis_core.field.QM31.mul both q5
  let occupancy2 ← Array.update occupancy1 1#usize q6
  let q7 ← aspis_core.field.QM31.mul one_minus inverse
  let q8 ← aspis_core.field.QM31.mul both q7
  let occupancy3 ← Array.update occupancy2 2#usize q8
  let i ← lift (Std.Usize.wrapping_add 2#usize 0#usize)
  let q9 ← Array.index_usize opened i
  let q10 ← aspis_core.field.QM31.mul one_minus q9
  let q11 ← aspis_core.field.QM31.mul both q10
  let i1 ← lift (Std.Usize.wrapping_add 3#usize 0#usize)
  let occupancy4 ← Array.update occupancy3 i1 q11
  let i2 ← lift (Std.Usize.wrapping_add 2#usize 1#usize)
  let q12 ← Array.index_usize opened i2
  let q13 ← aspis_core.field.QM31.mul one_minus q12
  let q14 ← aspis_core.field.QM31.mul both q13
  let i3 ← lift (Std.Usize.wrapping_add 3#usize 1#usize)
  let occupancy5 ← Array.update occupancy4 i3 q14
  let i4 ← lift (Std.Usize.wrapping_add 2#usize 2#usize)
  let q15 ← Array.index_usize opened i4
  let q16 ← aspis_core.field.QM31.mul one_minus q15
  let q17 ← aspis_core.field.QM31.mul both q16
  let i5 ← lift (Std.Usize.wrapping_add 3#usize 2#usize)
  let occupancy6 ← Array.update occupancy5 i5 q17
  let i6 ← lift (Std.Usize.wrapping_add 2#usize 3#usize)
  let q18 ← Array.index_usize opened i6
  let q19 ← aspis_core.field.QM31.mul one_minus q18
  let q20 ← aspis_core.field.QM31.mul both q19
  let i7 ← lift (Std.Usize.wrapping_add 3#usize 3#usize)
  let occupancy7 ← Array.update occupancy6 i7 q20
  let i8 ← lift (Std.Usize.wrapping_add 2#usize 4#usize)
  let q21 ← Array.index_usize opened i8
  let q22 ← aspis_core.field.QM31.mul one_minus q21
  let q23 ← aspis_core.field.QM31.mul both q22
  let i9 ← lift (Std.Usize.wrapping_add 3#usize 4#usize)
  let occupancy8 ← Array.update occupancy7 i9 q23
  let i10 ← lift (Std.Usize.wrapping_add 2#usize 5#usize)
  let q24 ← Array.index_usize opened i10
  let q25 ← aspis_core.field.QM31.mul one_minus q24
  let q26 ← aspis_core.field.QM31.mul both q25
  let i11 ← lift (Std.Usize.wrapping_add 3#usize 5#usize)
  let occupancy9 ← Array.update occupancy8 i11 q26
  let i12 ← lift (Std.Usize.wrapping_add 2#usize 6#usize)
  let q27 ← Array.index_usize opened i12
  let q28 ← aspis_core.field.QM31.mul one_minus q27
  let q29 ← aspis_core.field.QM31.mul both q28
  let i13 ← lift (Std.Usize.wrapping_add 3#usize 6#usize)
  let occupancy10 ← Array.update occupancy9 i13 q29
  let i14 ← lift (Std.Usize.wrapping_add 2#usize 7#usize)
  let q30 ← Array.index_usize opened i14
  let q31 ← aspis_core.field.QM31.mul one_minus q30
  let q32 ← aspis_core.field.QM31.mul both q31
  let i15 ← lift (Std.Usize.wrapping_add 3#usize 7#usize)
  let occupancy11 ← Array.update occupancy10 i15 q32
  let q33 ← Array.index_usize opened 10#usize
  let q34 ← aspis_core.field.QM31.mul q33 one_minus
  let q35 ← aspis_core.field.QM31.mul input_occupancy q34
  let q36 ← reference_terminal.lift_m31 expected_output
  let q37 ← aspis_core.field.QM31.sub occupied q36
  let q38 ← aspis_core.field.QM31.mul output_occupancy q37
  let q39 ← aspis_core.field.QM31.add q35 q38
  Array.update occupancy11 11#usize q39

/-- [pv_b3p6_reference227::reference_terminal::add_occupancy_lanes]:
    Source: 'reference_terminal.rs', lines 987:0-1011:1 -/
def reference_terminal.add_occupancy_lanes
  (packed : Array aspis_core.field.QM31 24#usize)
  (public1 : reference_terminal.SemanticPublic)
  (openings : aspis_statement.state_only_poseidon.StateOnlyPoseidonOpenings)
  (selectors : reference_copy_terminal.Selectors) :
  Result (Array aspis_core.field.QM31 24#usize)
  := do
  let i ← reference_terminal.INPUT_OCCUPANCY_ROW
  let input_occupancy ← reference_copy_terminal.Selectors.row selectors i
  let i1 ← reference_terminal.OUTPUT_OCCUPANCY_ROW
  let output_occupancy ← reference_copy_terminal.Selectors.row selectors i1
  let expected_output ←
    reference_terminal.variant_expected_output public1.variant
  let occupancy ←
    reference_terminal.occupancy_lanes_literal input_occupancy output_occupancy
      expected_output openings.z
  reference_terminal.add_preweighted packed 0#usize occupancy

attribute [local irreducible] aspis_core.field.QM31.add aspis_core.field.QM31.sub aspis_core.field.QM31.square aspis_core.field.QM31.mul aspis_core.field.QM31.mul_m31 Array.index_usize Array.update reference_terminal.read227 reference_terminal.reconstruct_10 reference_terminal.add_preweighted reference_copy_terminal.Selectors.row

theorem value_source_equation10_14 (packed : Array aspis_core.field.QM31 24#usize)
    (openings : aspis_statement.state_only_poseidon.StateOnlyPoseidonOpenings)
    (selectors : reference_copy_terminal.Selectors) (state : ValueState9) :
    value_source_tail10_14 packed openings selectors state =
      value_owned_stage9_14 packed openings selectors state := by
  unfold value_source_tail10_14 value_owned_stage9_14 value_read_context9_14
  rfl

#print axioms value_source_equation10_14
end PV_B3P_Binding10227
