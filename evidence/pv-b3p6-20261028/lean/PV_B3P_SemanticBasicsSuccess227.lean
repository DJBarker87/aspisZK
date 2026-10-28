import PV_B3P_IntervalSuccess227
namespace PV_B3P_Success227
open Aeneas Aeneas.Std PV_B3P_227
set_option autoImplicit false

theorem read_total {N : Usize} (xs : Array aspis_core.field.QM31 N) (i : Usize)
    (hi : i.val<N.val) : Success (reference_terminal.read227 xs i) := index xs i hi

#print axioms read_total

theorem lift_m31_total (value : aspis_core.field.M31) :
    Success (reference_terminal.lift_m31 value) := by
  unfold reference_terminal.lift_m31
  apply bind
  · exact ok _
  intro c
  exact ok _

theorem initial_lane_total (lane : Usize)
    (full_or_rate full : host_terminal_field.PreparedQm31Multiplier)
    (value : aspis_core.field.QM31) :
    Success (reference_terminal.initial_lane227 lane full_or_rate full value) := by
  unfold reference_terminal.initial_lane227
  split <;> apply total_host_terminal_field_PreparedQm31Multiplier_mul

theorem initial_variant_total (variant : reference_terminal.CompiledVariant)
    (high27 high28 high29 : aspis_core.field.QM31) :
    Success (reference_terminal.initial_variant_selectors variant high27 high28 high29) := by
  unfold reference_terminal.initial_variant_selectors
  cases variant with
  | PrivateTransfer =>
    apply bind
    · apply qadd
    intro q
    exact ok _
  | Withdrawal =>
    apply bind
    · apply qadd
    intro q
    apply bind
    · apply qadd
    intro q1
    exact ok _

theorem absorption_lane_total (lane : Usize)
    (low fixed chunk_two chunk_eight nodes opened : aspis_core.field.QM31) :
    Success (reference_terminal.absorption_lane227 lane low fixed chunk_two chunk_eight nodes opened) := by
  unfold reference_terminal.absorption_lane227
  apply bind
  · split
    · exact ok _
    · split
      · apply qadd
      · apply bind
        · apply qadd
        intro q
        apply bind
        · apply qadd
        intro q1
        apply qadd
  intro blocks
  apply bind
  · apply qmul
  intro q
  apply qmul

#print axioms lift_m31_total
#print axioms initial_lane_total
#print axioms initial_variant_total
#print axioms absorption_lane_total
end PV_B3P_Success227
