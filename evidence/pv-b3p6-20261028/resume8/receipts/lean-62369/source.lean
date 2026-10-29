import PV_B3P_DigestCps8227
namespace PV_B3P_Success227
open Aeneas Aeneas.Std PV_B3P_227
set_option autoImplicit false

attribute [local irreducible] reference_terminal.public_digest_lanes reference_terminal.add_schedule_lanes reference_terminal.add_path_lanes reference_terminal.add_value_lanes reference_terminal.add_occupancy_lanes reference_terminal.add_preweighted reference_terminal.scalar_lanes reference_copy_terminal.Selectors.row

/-- Compose the actual semantic accumulator from the checked stage laws.
All public fields, openings and selector values remain symbolic. -/
theorem semantic_success8 (p : reference_terminal.SemanticPublic)
    (openings : aspis_statement.state_only_poseidon.StateOnlyPoseidonOpenings)
    (selectors : reference_copy_terminal.Selectors) :
    Success (reference_terminal.semantic_packed p openings selectors) := by
  unfold reference_terminal.semantic_packed
  apply bind
  · exact total_reference_terminal_add_schedule_lanes _ p openings selectors
  intro packed1
  apply bind
  · exact total_reference_terminal_add_path_lanes packed1 openings selectors
  intro packed2
  apply bind
  · exact total_reference_terminal_add_value_lanes packed2 openings selectors
  intro packed3
  apply bind
  · exact total_reference_terminal_add_occupancy_lanes packed3 p openings selectors
  intro packed4
  apply bind
  · exact public_digest_success8 p openings selectors
  intro digests
  apply bind
  · apply preweighted_total <;> scalar_tac
  intro packed5
  apply bind
  · apply index <;> scalar_tac
  intro asset
  apply bind
  · exact lift_m31_total p.asset_id
  intro expected_asset
  apply bind
  · exact qsub asset expected_asset
  intro difference
  apply lift_total
  apply lift_total
  apply bind
  · apply row_total
    apply row_address_bound <;> scalar_tac
  intro input_selector
  apply bind
  · exact qmul input_selector difference
  intro input_asset
  apply lift_total
  apply lift_total
  apply bind
  · apply row_total
    apply row_address_bound <;> scalar_tac
  intro output_selector
  apply bind
  · exact qmul output_selector difference
  intro output_scalar
  apply lift_total
  apply lift_total
  apply bind
  · apply row_total
    apply row_address_bound <;> scalar_tac
  intro private_selector
  apply bind
  · exact qmul private_selector difference
  intro private_transfer_term
  apply lift_total
  apply lift_total
  apply lift_total
  apply bind
  · apply row_total
    apply row_left_address_bound <;>
      first | scalar_tac | (simp only [reference_terminal.VALUE_AUXILIARY_BLOCK]; scalar_tac)
  intro withdrawal_selector
  apply bind
  · apply index <;> scalar_tac
  intro amount
  apply bind
  · exact lift_m31_total _
  intro expected_amount
  apply bind
  · exact qsub amount expected_amount
  intro amount_difference
  apply bind
  · exact qmul withdrawal_selector amount_difference
  intro withdrawal_term
  apply bind
  · exact scalar_total p.variant _ input_asset output_scalar private_transfer_term withdrawal_term
  intro scalars
  apply preweighted_total <;> scalar_tac

#print axioms semantic_success8
end PV_B3P_Success227
