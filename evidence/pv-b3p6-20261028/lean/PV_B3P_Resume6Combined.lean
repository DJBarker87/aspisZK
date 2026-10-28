import PV_B3P_DotSuccess227
import PV_B3P_EqualitySuccess227
import PV_B3P_ReverseSuccess227
import PV_B3P_GlobalSumsSuccess227
import PV_B3P_HostPackSuccess227
import PV_B3P_RefPackSuccess227
import PV_B3P_AbsorptionSuccess227
import PV_B3P_PublicSuccess227
import PV_B3P_SelectValue227
import PV_B3P_C1Success227
import PV_B3P_MaskSuccess227
namespace PV_B3P_Success227
open Aeneas Aeneas.Std PV_B3P_227
set_option autoImplicit false

def seed_public : reference_terminal.SemanticPublic := {
  variant := .PrivateTransfer
  pool := Array.repeat 32#usize 0#u8
  deployment_domain := Array.repeat 32#usize 0#u8
  anchor := Array.repeat 8#usize 0#u32
  nullifier := Array.repeat 8#usize 0#u32
  asset_id := 0#u32
  recipient := some (Array.repeat 8#usize 0#u32)
  change := Array.repeat 8#usize 0#u32
  withdrawal_amount := none
  transition := {
    live_snapshot := {
      pool := Array.repeat 32#usize 0#u8
      deployment_domain := Array.repeat 32#usize 0#u8
      sequence := 0#u64, next_pair_index := 0#u64
      current_root := Array.repeat 8#usize 0#u32, frontier := empty_frontier}
    candidate_afterstate := {
      next_pair_index := 1#u64, next_root := Array.repeat 8#usize 0#u32
      next_frontier := empty_frontier}}}

/-- Unconditional successful nonvacuity of the emitted validator fragment.
This is deliberately not a claim about the full reference or installed op227. -/
theorem public_nonvacuity : ∃ p : reference_terminal.SemanticPublic,
    p.withdrawal_amount=none ∧ reference_terminal.validate_transition p=.ok (.Ok ()) :=
  ⟨valid_public seed_public,rfl,public_transition_success seed_public⟩

#print axioms public_nonvacuity

/-- The actual extracted preparation calls all succeed for the symbolic public
family, arbitrary claims and arbitrary point. The remaining residual evaluators
are not included, so this is not full reference or installed nonvacuity. -/
theorem preparation_success (p : reference_terminal.SemanticPublic)
    (claims : Array (Array aspis_core.field.QM31 29#usize) 3#usize)
    (point : Array aspis_core.field.QM31 10#usize) :
    ∃ selected a0 a1 a2 mask selectors,
      reference_terminal.validate_transition (valid_public p)=.ok (.Ok ()) ∧
      reference_terminal.select227 claims=.ok selected ∧
      reference_terminal.select_c1_227 selected 0#usize=.ok a0 ∧
      reference_terminal.select_c1_227 selected 1#usize=.ok a1 ∧
      reference_terminal.select_c1_227 selected 2#usize=.ok a2 ∧
      reference_terminal.composition_parts_loop0 selected
        (Array.repeat 10#usize aspis_core.field.QM31.ZERO) 0#usize=.ok mask ∧
      reference_copy_terminal.Selectors.boxed_at_point point=.ok selectors := by
  obtain ⟨selected,hselected,_⟩ := PV_B3P_SelectValue227.nonvacuity claims
  obtain ⟨a0,ha0⟩ := total_reference_terminal_select_c1_227 selected 0#usize (by change 0<3; omega)
  obtain ⟨a1,ha1⟩ := total_reference_terminal_select_c1_227 selected 1#usize (by change 1<3; omega)
  obtain ⟨a2,ha2⟩ := total_reference_terminal_select_c1_227 selected 2#usize (by change 2<3; omega)
  obtain ⟨mask,hmask⟩ := mask_loop_total selected
    (Array.repeat 10#usize aspis_core.field.QM31.ZERO) 0#usize (by change 0≤10; omega)
  obtain ⟨selectors,hselectors⟩ := boxed_selectors_total point
  exact ⟨selected,a0,a1,a2,mask,selectors,public_transition_success p,
    hselected,ha0,ha1,ha2,hmask,hselectors⟩

#print axioms preparation_success
end PV_B3P_Success227
