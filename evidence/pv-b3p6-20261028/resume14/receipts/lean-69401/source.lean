import PV_B3P_LinkDefinitions13227
namespace PV_B3P_Correct14227
open Aeneas Aeneas.Std PV_B3P_227 PV_B3P_Links13227
set_option autoImplicit false
abbrev Q := aspis_core.field.QM31
abbrev SelectorFn := Array Q 10#usize → Result aspis_statement.state_only_poseidon.StateOnlyPoseidonSelectors
/-- Constructor model parameterized by its actual high-selector prefix length.
The legacy constructor chooses 49; the terminal caller chooses 57. -/
def constructor14 (blocks : Usize) (point : Array Q 10#usize) :
    Result aspis_statement.state_only_poseidon.StateOnlyPoseidonSelectors := do
  let selectors ← reference_copy_terminal.Selectors.at_point point
  let block ← reference_terminal.sum_interval227 selectors.high Q.ZERO 0#usize blocks
  .ok { block := block, «local» := selectors.low }
/-- Corrected constructor equality requires the target layout. This condition
is on the constructor, never a restriction on arbitrary adversarial points. -/
def PV_B3P_Link_constructor_on_layout (source : Usize → SelectorFn) : Prop :=
  ∀ blocks, blocks = 57#usize → source blocks = selector_reference13
/-- Additional caller obligation rules out selecting the legacy 49-block body. -/
def PV_B3P_Link_constructor_call_layout (selected_blocks : Usize) : Prop :=
  selected_blocks = 57#usize
/-- Own-1 still must associate the actual source caller to this selected model. -/
def PV_B3P_Link_constructor_native (native : SelectorFn) (source : Usize → SelectorFn)
    (selected_blocks : Usize) : Prop := native = source selected_blocks

theorem constructor_target14 : constructor14 57#usize = selector_reference13 := by
  funext point
  unfold constructor14 selector_reference13 reference_terminal.poseidon_selectors
  rfl

theorem constructor_on_layout14 : PV_B3P_Link_constructor_on_layout constructor14 := by
  intro blocks same
  subst blocks
  exact constructor_target14

theorem constructor_at_call14 (native : SelectorFn) (source : Usize → SelectorFn)
    (blocks : Usize) (body : PV_B3P_Link_constructor_on_layout source)
    (layout : PV_B3P_Link_constructor_call_layout blocks)
    (association : PV_B3P_Link_constructor_native native source blocks) :
    PV_B3P_Link_poseidon_at_point native :=
  Eq.trans association (body blocks layout)

theorem constructor_joint_witness14 :
    ∃ native source blocks, PV_B3P_Link_constructor_on_layout source ∧
      PV_B3P_Link_constructor_call_layout blocks ∧
      PV_B3P_Link_constructor_native native source blocks :=
  ⟨constructor14 57#usize,constructor14,57#usize,constructor_on_layout14,rfl,rfl⟩
#print axioms constructor_target14
#print axioms constructor_on_layout14
#print axioms constructor_at_call14
#print axioms constructor_joint_witness14
end PV_B3P_Correct14227
