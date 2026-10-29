import PV_B3P_ValueCpsBridge10227
namespace PV_B3P_Binding10227
open Aeneas Aeneas.Std PV_B3P_227 PV_B3P_Binding9227
set_option autoImplicit false

attribute [local irreducible] aspis_core.field.QM31.add aspis_core.field.QM31.sub aspis_core.field.QM31.square aspis_core.field.QM31.mul aspis_core.field.QM31.mul_m31 Array.index_usize Array.update reference_terminal.read227 reference_terminal.reconstruct_10 reference_terminal.add_preweighted reference_copy_terminal.Selectors.row

theorem value_selector_frame10_01 {β : Type} (packed : Array aspis_core.field.QM31 24#usize)
    (openings : aspis_statement.state_only_poseidon.StateOnlyPoseidonOpenings)
    (selectors : reference_copy_terminal.Selectors)
    (selector : aspis_core.field.QM31) (range_input : Array aspis_core.field.QM31 33#usize)
    (f : ValueState9 → Result β) :
    (value_owned_stage9_01 packed openings selectors (selector,range_input) >>= f) =
    (value_owned_stage9_01 packed openings selectors (selector,range_input) >>= (fun next => f (selector,next.2))) := by
  unfold value_owned_stage9_01 value_read_context9_01
  simp only [PV_B3P_Ordered227.bind_assoc,bind_tc_ok]
#print axioms value_selector_frame10_01

theorem value_selector_frame10_02 {β : Type} (packed : Array aspis_core.field.QM31 24#usize)
    (openings : aspis_statement.state_only_poseidon.StateOnlyPoseidonOpenings)
    (selectors : reference_copy_terminal.Selectors)
    (selector : aspis_core.field.QM31) (range_input : Array aspis_core.field.QM31 33#usize)
    (f : ValueState9 → Result β) :
    (value_owned_stage9_02 packed openings selectors (selector,range_input) >>= f) =
    (value_owned_stage9_02 packed openings selectors (selector,range_input) >>= (fun next => f (selector,next.2))) := by
  unfold value_owned_stage9_02 value_read_context9_02
  simp only [PV_B3P_Ordered227.bind_assoc,bind_tc_ok]
#print axioms value_selector_frame10_02

theorem value_selector_frame10_03 {β : Type} (packed : Array aspis_core.field.QM31 24#usize)
    (openings : aspis_statement.state_only_poseidon.StateOnlyPoseidonOpenings)
    (selectors : reference_copy_terminal.Selectors)
    (selector : aspis_core.field.QM31) (range_input : Array aspis_core.field.QM31 33#usize)
    (f : ValueState9 → Result β) :
    (value_owned_stage9_03 packed openings selectors (selector,range_input) >>= f) =
    (value_owned_stage9_03 packed openings selectors (selector,range_input) >>= (fun next => f (selector,next.2))) := by
  unfold value_owned_stage9_03 value_read_context9_03
  simp only [PV_B3P_Ordered227.bind_assoc,bind_tc_ok]
#print axioms value_selector_frame10_03

theorem value_selector_frame10_04 {β : Type} (packed : Array aspis_core.field.QM31 24#usize)
    (openings : aspis_statement.state_only_poseidon.StateOnlyPoseidonOpenings)
    (selectors : reference_copy_terminal.Selectors)
    (selector : aspis_core.field.QM31) (range_input : Array aspis_core.field.QM31 33#usize)
    (f : ValueState9 → Result β) :
    (value_owned_stage9_04 packed openings selectors (selector,range_input) >>= f) =
    (value_owned_stage9_04 packed openings selectors (selector,range_input) >>= (fun next => f (selector,next.2))) := by
  unfold value_owned_stage9_04 value_read_context9_04
  simp only [PV_B3P_Ordered227.bind_assoc,bind_tc_ok]
#print axioms value_selector_frame10_04

theorem value_selector_frame10_05 {β : Type} (packed : Array aspis_core.field.QM31 24#usize)
    (openings : aspis_statement.state_only_poseidon.StateOnlyPoseidonOpenings)
    (selectors : reference_copy_terminal.Selectors)
    (selector : aspis_core.field.QM31) (range_input : Array aspis_core.field.QM31 33#usize)
    (f : ValueState9 → Result β) :
    (value_owned_stage9_05 packed openings selectors (selector,range_input) >>= f) =
    (value_owned_stage9_05 packed openings selectors (selector,range_input) >>= (fun next => f (selector,next.2))) := by
  unfold value_owned_stage9_05 value_read_context9_05
  simp only [PV_B3P_Ordered227.bind_assoc,bind_tc_ok]
#print axioms value_selector_frame10_05

theorem value_selector_frame10_06 {β : Type} (packed : Array aspis_core.field.QM31 24#usize)
    (openings : aspis_statement.state_only_poseidon.StateOnlyPoseidonOpenings)
    (selectors : reference_copy_terminal.Selectors)
    (selector : aspis_core.field.QM31) (range_input : Array aspis_core.field.QM31 33#usize)
    (f : ValueState9 → Result β) :
    (value_owned_stage9_06 packed openings selectors (selector,range_input) >>= f) =
    (value_owned_stage9_06 packed openings selectors (selector,range_input) >>= (fun next => f (selector,next.2))) := by
  unfold value_owned_stage9_06 value_read_context9_06
  simp only [PV_B3P_Ordered227.bind_assoc,bind_tc_ok]
#print axioms value_selector_frame10_06

theorem value_selector_frame10_07 {β : Type} (packed : Array aspis_core.field.QM31 24#usize)
    (openings : aspis_statement.state_only_poseidon.StateOnlyPoseidonOpenings)
    (selectors : reference_copy_terminal.Selectors)
    (selector : aspis_core.field.QM31) (range_input : Array aspis_core.field.QM31 33#usize)
    (f : ValueState9 → Result β) :
    (value_owned_stage9_07 packed openings selectors (selector,range_input) >>= f) =
    (value_owned_stage9_07 packed openings selectors (selector,range_input) >>= (fun next => f (selector,next.2))) := by
  unfold value_owned_stage9_07 value_read_context9_07
  simp only [PV_B3P_Ordered227.bind_assoc,bind_tc_ok]
#print axioms value_selector_frame10_07

theorem value_selector_frame10_08 {β : Type} (packed : Array aspis_core.field.QM31 24#usize)
    (openings : aspis_statement.state_only_poseidon.StateOnlyPoseidonOpenings)
    (selectors : reference_copy_terminal.Selectors)
    (selector : aspis_core.field.QM31) (range_input : Array aspis_core.field.QM31 33#usize)
    (f : ValueState9 → Result β) :
    (value_owned_stage9_08 packed openings selectors (selector,range_input) >>= f) =
    (value_owned_stage9_08 packed openings selectors (selector,range_input) >>= (fun next => f (selector,next.2))) := by
  unfold value_owned_stage9_08 value_read_context9_08
  simp only [PV_B3P_Ordered227.bind_assoc,bind_tc_ok]
#print axioms value_selector_frame10_08

theorem value_selector_frame10_09 {β : Type} (packed : Array aspis_core.field.QM31 24#usize)
    (openings : aspis_statement.state_only_poseidon.StateOnlyPoseidonOpenings)
    (selectors : reference_copy_terminal.Selectors)
    (selector : aspis_core.field.QM31) (range_input : Array aspis_core.field.QM31 33#usize)
    (f : ValueState9 → Result β) :
    (value_owned_stage9_09 packed openings selectors (selector,range_input) >>= f) =
    (value_owned_stage9_09 packed openings selectors (selector,range_input) >>= (fun next => f (selector,next.2))) := by
  unfold value_owned_stage9_09 value_read_context9_09
  simp only [PV_B3P_Ordered227.bind_assoc,bind_tc_ok]
#print axioms value_selector_frame10_09

theorem value_selector_frame10_10 {β : Type} (packed : Array aspis_core.field.QM31 24#usize)
    (openings : aspis_statement.state_only_poseidon.StateOnlyPoseidonOpenings)
    (selectors : reference_copy_terminal.Selectors)
    (selector : aspis_core.field.QM31) (range_input : Array aspis_core.field.QM31 33#usize)
    (f : ValueState9 → Result β) :
    (value_owned_stage9_10 packed openings selectors (selector,range_input) >>= f) =
    (value_owned_stage9_10 packed openings selectors (selector,range_input) >>= (fun next => f (selector,next.2))) := by
  unfold value_owned_stage9_10 value_read_context9_10
  simp only [PV_B3P_Ordered227.bind_assoc,bind_tc_ok]
#print axioms value_selector_frame10_10

theorem value_selector_frame10_11 {β : Type} (packed : Array aspis_core.field.QM31 24#usize)
    (openings : aspis_statement.state_only_poseidon.StateOnlyPoseidonOpenings)
    (selectors : reference_copy_terminal.Selectors)
    (selector : aspis_core.field.QM31) (range_input : Array aspis_core.field.QM31 33#usize)
    (f : ValueState9 → Result β) :
    (value_owned_stage9_11 packed openings selectors (selector,range_input) >>= f) =
    (value_owned_stage9_11 packed openings selectors (selector,range_input) >>= (fun next => f (selector,next.2))) := by
  unfold value_owned_stage9_11 value_read_context9_11
  simp only [PV_B3P_Ordered227.bind_assoc,bind_tc_ok]
#print axioms value_selector_frame10_11

theorem value_selector_frame10_12 {β : Type} (packed : Array aspis_core.field.QM31 24#usize)
    (openings : aspis_statement.state_only_poseidon.StateOnlyPoseidonOpenings)
    (selectors : reference_copy_terminal.Selectors)
    (selector : aspis_core.field.QM31) (range_input : Array aspis_core.field.QM31 33#usize)
    (f : ValueState9 → Result β) :
    (value_owned_stage9_12 packed openings selectors (selector,range_input) >>= f) =
    (value_owned_stage9_12 packed openings selectors (selector,range_input) >>= (fun next => f (selector,next.2))) := by
  unfold value_owned_stage9_12 value_read_context9_12
  simp only [PV_B3P_Ordered227.bind_assoc,bind_tc_ok]
#print axioms value_selector_frame10_12

theorem value_selector_frame10_13 {β : Type} (packed : Array aspis_core.field.QM31 24#usize)
    (openings : aspis_statement.state_only_poseidon.StateOnlyPoseidonOpenings)
    (selectors : reference_copy_terminal.Selectors)
    (selector : aspis_core.field.QM31) (range_input : Array aspis_core.field.QM31 33#usize)
    (f : ValueState9 → Result β) :
    (value_owned_stage9_13 packed openings selectors (selector,range_input) >>= f) =
    (value_owned_stage9_13 packed openings selectors (selector,range_input) >>= (fun next => f (selector,next.2))) := by
  unfold value_owned_stage9_13 value_read_context9_13
  simp only [PV_B3P_Ordered227.bind_assoc,bind_tc_ok]
#print axioms value_selector_frame10_13
end PV_B3P_Binding10227
