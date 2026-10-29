import PV_B3P_ValueRead914227
import PV_B3P_PreweightedLoop12227
namespace PV_B3P_Binding12227
open Aeneas Aeneas.Std PV_B3P_227 PV_B3P_Binding9227 Result
set_option autoImplicit false
def value_context12_14 (operation : {N : Usize} → Array aspis_core.field.QM31 24#usize → Usize → Array aspis_core.field.QM31 N → Result (Array aspis_core.field.QM31 24#usize)) (source_read : ({N : Usize} → Array aspis_core.field.QM31 N → Usize → Result aspis_core.field.QM31)) (packed : Array aspis_core.field.QM31 24#usize)
    (openings : aspis_statement.state_only_poseidon.StateOnlyPoseidonOpenings)
    (selectors : reference_copy_terminal.Selectors) (state : ValueState9) : Result (Array aspis_core.field.QM31 24#usize) := do
  let packed1 ← operation packed 49#usize state.2
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
  operation packed1 82#usize
    (Array.make 2#usize [ q179, q183 ] (by simp only [List.length_cons,List.length_nil]; rfl))
def value_stage12_14 (packed : Array aspis_core.field.QM31 24#usize)
    (openings : aspis_statement.state_only_poseidon.StateOnlyPoseidonOpenings)
    (selectors : reference_copy_terminal.Selectors) (state : ValueState9) : Result (Array aspis_core.field.QM31 24#usize) :=
  value_context12_14 (@source_preweighted12) (fun values i => Array.index_usize values i) packed openings selectors state
theorem value_stage_binding12_14 (packed : Array aspis_core.field.QM31 24#usize)
    (openings : aspis_statement.state_only_poseidon.StateOnlyPoseidonOpenings)
    (selectors : reference_copy_terminal.Selectors) (state : ValueState9) :
    value_direct_stage9_14 packed openings selectors state = value_stage12_14 packed openings selectors state :=
  congrArg (fun (operation : {N : Usize} → Array aspis_core.field.QM31 24#usize → Usize → Array aspis_core.field.QM31 N → Result (Array aspis_core.field.QM31 24#usize)) => value_context12_14 @operation
    (fun values i => Array.index_usize values i) packed openings selectors state) preweighted_operation_binding12
#print axioms value_stage_binding12_14
end PV_B3P_Binding12227
