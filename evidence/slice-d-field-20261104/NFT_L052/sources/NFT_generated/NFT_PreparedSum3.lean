import RPv_AspisR1_PoseidonPreparedSum3ActualValue
import RPv_AspisR1PoseidonPreparedChannelRunStepLocal
import RPv_AspisR1PoseidonPreparedChannelLoopExact
import NFT_ChannelModel
set_option autoImplicit false
noncomputable section
namespace NFT_PreparedSum3
open Aeneas Aeneas.Std Result AspisR1SelectedMaskProbe
abbrev Q := field.QM31
abbrev Prepared := field.PreparedQm31Multiplier
abbrev Left := Array Prepared 3#usize
abbrev Right := Array Q 3#usize
abbrev Canonical := AspisR1.ExtractedMaskTowerAdd.CanonicalQM
abbrev PreparedFor := AspisR1.ExtractedMaskPreparedState.PreparedFor
abbrev decode := AspisR1.PoseidonPreparedKaratsubaValue.decodeQM

def leftAt (a : Left) (i : Fin 3) : Prepared :=
  a.val[(AspisR1PoseidonPreparedIndexProductBounds.uFin i).val]'(by
    have h:=AspisR1PoseidonPreparedIndexProductBounds.uFin_val i
    simpa [a.property,h] using i.isLt)
def rightAt (a : Right) (i : Fin 3) : Q :=
  a.val[(AspisR1PoseidonPreparedIndexProductBounds.uFin i).val]'(by
    have h:=AspisR1PoseidonPreparedIndexProductBounds.uFin_val i
    simpa [a.property,h] using i.isLt)

theorem source (left : Left) (right : Right)
    (prepared : ∀ i : Fin 3, ∃ x : Q, Canonical x ∧ PreparedFor (leftAt left i) x)
    (canonical : ∀ i : Fin 3, Canonical (rightAt right i)) :
    ∃ out x0 x1 x2 : Q,
      AspisR1PoseidonPreparedSum3Source.field.qm31_sum_products3_prepared left right=ok out ∧
      Canonical out ∧ PreparedFor (leftAt left 0) x0 ∧ PreparedFor (leftAt left 1) x1 ∧
      PreparedFor (leftAt left 2) x2 ∧
      decode out=decode x0*decode (rightAt right 0)+decode x1*decode (rightAt right 1)+decode x2*decode (rightAt right 2) :=
  AspisR1.PoseidonPreparedSum3ActualValue.actual_sum3_value left right prepared canonical

/-- The constructor law is applied to each actual input, not assumed as a
successful cached result. This is the caller-established prepared domain. -/
theorem constructor_domain (x : Q) (canonical : Canonical x) :
    ∃ p : Prepared, field.PreparedQm31Multiplier.new x=ok p ∧ PreparedFor p x :=
  AspisR1.ExtractedMaskPreparedState.current_prepared_new x canonical

#print axioms source
#print axioms constructor_domain
#print axioms AspisR1PoseidonPreparedChannelRunStepLocal.runStep_success
#print axioms AspisR1PoseidonPreparedChannelLoopExact.loop_success_fuel
end NFT_PreparedSum3
