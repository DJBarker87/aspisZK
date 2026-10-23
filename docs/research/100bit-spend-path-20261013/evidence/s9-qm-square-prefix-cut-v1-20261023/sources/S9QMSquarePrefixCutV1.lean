import S9QMSquareHelperSourceBridgeV1
import S9ResultSuccessReflectionV1
import S9BodyPrefixWitnessV1
import S3S9ScalarFactorKpowersReadV1

set_option autoImplicit false
open Aeneas Aeneas.Std Result

namespace AspisR1S9QMSquarePrefixCutV1

abbrev Q := AspisR1S9HelperP6.field.QM31
abbrev XQ := AspisR1S9SquareMulQMCutV1.field.QM31
abbrev Sem := AspisR1S9HelperP6PowerSemanticsV1.currentQMSemantics

local instance currentFieldOpsForSemantics : AspisR1S9HelperP6.FieldOps :=
  AspisR1S9HelperP6PowerSemanticsV1.currentFieldOps

private theorem toCut_fromCut (x : XQ) :
    AspisR1S9QMSquareHelperSourceBridgeV1.toCut
      (AspisR1S9QMSquareHelperSourceBridgeV1.fromCut x) = x := by
  cases x with
  | mk c0 c1 => cases c0 with | mk a b => cases c1 with | mk c d => rfl

private theorem generated_to_current_qm (x : Q) :
    AspisR1S9GeneratedWideMulQM31V2.toQM x =
      AspisR1S9HelperP6PowerSemanticsV1.helperToCurrentQM x := by
  cases x <;> rfl

/-- Invert the accepted full-Result source bridge at the same canonical
operand. A successful installed helper square therefore identifies the exact
returned value of the extracted cut square. -/
theorem source_square_same_success (x z : Q)
    (hx : Sem.canonical x)
    (hcall : @AspisR1S9HelperP6.FieldOps.qmSquare
      AspisR1S9ConcreteFieldOpsV1.concreteFieldOps x = .ok z) :
    AspisR1S9SquareMulQMCutV1.field.QM31.square
      (AspisR1S9QMSquareHelperSourceBridgeV1.toCut x) =
      .ok (AspisR1S9QMSquareHelperSourceBridgeV1.toCut z) := by
  have hmap := AspisR1S9QMSquareHelperSourceBridgeV1.actual_qm_square_maps_to_installed_helper x hx
  change AspisR1S9QMSquareHelperSourceBridgeV1.mapResult
      AspisR1S9QMSquareHelperSourceBridgeV1.fromCut
      (AspisR1S9SquareMulQMCutV1.field.QM31.square
        (AspisR1S9QMSquareHelperSourceBridgeV1.toCut x)) =
    AspisR1S9ConcreteFieldOpsV1.actualQMSquare x at hmap
  have hcall' : AspisR1S9ConcreteFieldOpsV1.actualQMSquare x = .ok z := by
    rw [← AspisR1S9ConcreteFieldOpsV1.concrete_qmSquare_dispatch x]
    exact hcall
  rw [hcall'] at hmap
  have hmap' : AspisR1S9ResultSuccessReflectionV1.mapResult
      AspisR1S9QMSquareHelperSourceBridgeV1.fromCut
      (AspisR1S9SquareMulQMCutV1.field.QM31.square
        (AspisR1S9QMSquareHelperSourceBridgeV1.toCut x)) = .ok z := by
    change AspisR1S9QMSquareHelperSourceBridgeV1.mapResult
      AspisR1S9QMSquareHelperSourceBridgeV1.fromCut
      (AspisR1S9SquareMulQMCutV1.field.QM31.square
        (AspisR1S9QMSquareHelperSourceBridgeV1.toCut x)) = .ok z
    exact hmap
  obtain ⟨z', hsource, hfrom⟩ :=
    (AspisR1S9ResultSuccessReflectionV1.mapResult_ok_iff
      AspisR1S9QMSquareHelperSourceBridgeV1.fromCut _ z).mp hmap'
  have hz' : z' = AspisR1S9QMSquareHelperSourceBridgeV1.toCut z := by
    have hc := congrArg AspisR1S9QMSquareHelperSourceBridgeV1.toCut hfrom
    rw [toCut_fromCut] at hc
    exact hc
  rw [hz'] at hsource
  exact hsource

/-- The square operations reached in the exact successful concrete body prefix
are the same-result operations in the extracted source cut. q2 canonicality
comes from the same successful kpowers array read; q4/q8 canonicality comes
from this prefix's actual high array. No alternate operation record or extra
square-success premise is introduced. -/
theorem active_body_square_prefix_same_results
    {ap0 ap1 : AspisR1S9BodyPrefixSemanticsV1.W}
    {extra : Array Q (2#usize)} {side : Std.Usize}
    {iterNext : core.ops.range.Range Std.Usize} {weights0 : AspisR1S9BodyPrefixSemanticsV1.W}
    {flow : ControlFlow (core.ops.range.Range Std.Usize × AspisR1S9BodyPrefixSemanticsV1.W)
      AspisR1S9BodyPrefixSemanticsV1.W}
    (p : AspisR1S9BodyPrefixSemanticsV1.BodyPrefixWitness
      ap0 ap1 extra side iterNext weights0 flow)
    (hextra : ∀ (j : Std.Usize) (x : Q),
      Array.index_usize extra j = .ok x →
      AspisR1S9HighPowerPrefixSemanticsV1.CanonicalQ x) :
    (AspisR1S9SquareMulQMCutV1.field.QM31.square
      (AspisR1S9QMSquareHelperSourceBridgeV1.toCut p.q2) =
        .ok (AspisR1S9QMSquareHelperSourceBridgeV1.toCut p.q4)) ∧
    (AspisR1S9SquareMulQMCutV1.field.QM31.square
      (AspisR1S9QMSquareHelperSourceBridgeV1.toCut p.q4) =
        .ok (AspisR1S9QMSquareHelperSourceBridgeV1.toCut p.q8)) ∧
    (AspisR1S9SquareMulQMCutV1.field.QM31.square
      (AspisR1S9QMSquareHelperSourceBridgeV1.toCut p.q8) =
        .ok (AspisR1S9QMSquareHelperSourceBridgeV1.toCut p.q16)) := by
  have hseed : Sem.canonical p.q := by
    change AspisR1S9HighPowerPrefixSemanticsV1.CanonicalQ p.q
    exact hextra side p.q p.hq
  have hkpCurrent : @AspisR1S9HelperP6.weights.kpowers
      AspisR1S9HelperP6PowerSemanticsV1.currentQMOps (4#usize) p.q = .ok p.q1 := by
    exact (AspisR1S9ConcreteFieldOpsV1.kpowers_concrete_eq_current
      (4#usize) p.q).symm.trans p.hkp
  obtain ⟨hcan2, _⟩ :=
    AspisR1S9ScalarFactorKpowersReadV1.kpowers_success_read_current
      p.q p.q1 hseed hkpCurrent 2#usize p.q2 p.hq2
  have hread4 : Array.index_usize p.high 1#usize = .ok p.q4 := by
    rw [p.highArray]
    rfl
  have hread8 : Array.index_usize p.high 2#usize = .ok p.q8 := by
    rw [p.highArray]
    rfl
  have hcan4 : Sem.canonical p.q4 := by
    have h := p.highCanonical 1#usize p.q4 hread4
    change AspisR1CurrentWide.Proof.CanonicalQM
      (AspisR1S9HelperP6PowerSemanticsV1.helperToCurrentQM p.q4)
    rw [← generated_to_current_qm]
    exact h
  have hcan8 : Sem.canonical p.q8 := by
    have h := p.highCanonical 2#usize p.q8 hread8
    change AspisR1CurrentWide.Proof.CanonicalQM
      (AspisR1S9HelperP6PowerSemanticsV1.helperToCurrentQM p.q8)
    rw [← generated_to_current_qm]
    exact h
  exact ⟨source_square_same_success p.q2 p.q4 hcan2 p.hq4,
    source_square_same_success p.q4 p.q8 hcan4 p.hq8,
    source_square_same_success p.q8 p.q16 hcan8 p.hq16⟩

#print axioms source_square_same_success
#print axioms active_body_square_prefix_same_results

end AspisR1S9QMSquarePrefixCutV1
