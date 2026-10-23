import S9PairCallerBodyPrefixV1
import S9PairCallerStepOperationBridgeV1
import S9PairQMSquareToSourceV1
import S9QMSquarePrefixCutV1
import S9ConcreteQMMulAcceptedRootV1
import S3S9ConcreteSquareSemanticsV1
import KpowersCurrentQMSemanticsV1

set_option autoImplicit false
open Aeneas Aeneas.Std Result ControlFlow

namespace AspisR1S9PairActiveSquarePrefixV1

abbrev PairQ := AspisR1S9PairCallerStepV1.field.QM31
abbrev HelperQ := AspisR1S9HelperP6.field.QM31
abbrev Sem := AspisR1S9HelperP6PowerSemanticsV1.currentQMSemantics

local instance currentFieldOpsForSemantics : AspisR1S9HelperP6.FieldOps :=
  AspisR1S9HelperP6PowerSemanticsV1.currentFieldOps

private theorem generated_to_current (x : HelperQ) :
    AspisR1S9GeneratedWideMulQM31V2.toQM x =
      AspisR1S9HelperP6PowerSemanticsV1.helperToCurrentQM x := by
  cases x <;> rfl

private theorem accepted_canonical_to_semantic (x : HelperQ)
    (h : AspisR1.S9ConcreteArithmeticAcceptedRootV1.CanonicalQ x) :
    Sem.canonical x := by
  change AspisR1CurrentWide.Proof.CanonicalQM
    (AspisR1S9GeneratedWideMulQM31V2.toQM x) at h
  change AspisR1CurrentWide.Proof.CanonicalQM
    (AspisR1S9HelperP6PowerSemanticsV1.helperToCurrentQM x)
  rw [← generated_to_current]
  exact h

private theorem semantic_canonical_to_accepted (x : HelperQ)
    (h : Sem.canonical x) :
    AspisR1.S9ConcreteArithmeticAcceptedRootV1.CanonicalQ x := by
  change AspisR1CurrentWide.Proof.CanonicalQM
    (AspisR1S9HelperP6PowerSemanticsV1.helperToCurrentQM x) at h
  change AspisR1CurrentWide.Proof.CanonicalQM
    (AspisR1S9GeneratedWideMulQM31V2.toQM x)
  rw [generated_to_current]
  exact h

private theorem pair_one_to_helper :
    AspisR1S9PairCallerStepV1.toP6Q
      AspisR1S9PairCallerStepV1.field.QM31.ONE =
    AspisR1S9HelperP6.field.QM31.ONE := by
  unfold AspisR1S9PairCallerStepV1.toP6Q
    AspisR1S9PairCallerStepV1.toP6CM
    AspisR1S9PairCallerStepV1.toP6M
    AspisR1S9PairCallerStepV1.field.QM31.ONE
    AspisR1S9HelperP6.field.QM31.ONE
  rfl

private theorem pair_mul_success_canonical
    (x y z : PairQ)
    (hx : Sem.canonical (AspisR1S9PairCallerStepV1.toP6Q x))
    (hy : Sem.canonical (AspisR1S9PairCallerStepV1.toP6Q y))
    (h : AspisR1S9PairCallerStepV1.field.QM31.mul x y = .ok z) :
    Sem.canonical (AspisR1S9PairCallerStepV1.toP6Q z) := by
  have hmap := AspisR1S9PairCallerStepOperationBridgeV1.map_qm_mul x y
  rw [h] at hmap
  change Result.ok (AspisR1S9PairCallerStepV1.toP6Q z) =
    @AspisR1S9HelperP6.FieldOps.qmMul
      AspisR1S9ConcreteFieldOpsV1.concreteFieldOps
      (AspisR1S9PairCallerStepV1.toP6Q x)
      (AspisR1S9PairCallerStepV1.toP6Q y) at hmap
  have haccepted := AspisR1.S9ConcreteQMMulAcceptedRootV1.qmMul_success
    (AspisR1S9PairCallerStepV1.toP6Q x)
    (AspisR1S9PairCallerStepV1.toP6Q y)
    (AspisR1S9PairCallerStepV1.toP6Q z)
    (semantic_canonical_to_accepted _ hx)
    (semantic_canonical_to_accepted _ hy)
    hmap.symm
  exact accepted_canonical_to_semantic _ haccepted.1

private theorem pair_square_success_canonical
    (x z : PairQ)
    (hx : Sem.canonical (AspisR1S9PairCallerStepV1.toP6Q x))
    (h : AspisR1S9PairCallerStepV1.field.QM31.square x = .ok z) :
    Sem.canonical (AspisR1S9PairCallerStepV1.toP6Q z) := by
  have hmap := AspisR1S9PairCallerStepOperationBridgeV1.map_qm_square x
  rw [h] at hmap
  change Result.ok (AspisR1S9PairCallerStepV1.toP6Q z) =
    @AspisR1S9HelperP6.FieldOps.qmSquare
      AspisR1S9ConcreteFieldOpsV1.concreteFieldOps
      (AspisR1S9PairCallerStepV1.toP6Q x) at hmap
  obtain ⟨w, hw, hwcan, _⟩ :=
    AspisR1S9ConcreteSquareSemanticsV1.concrete_qmSquare_total
      (AspisR1S9PairCallerStepV1.toP6Q x) hx
  have hvalue : w = AspisR1S9PairCallerStepV1.toP6Q z :=
    Result.ok.inj (hw.symm.trans hmap.symm)
  rw [hvalue] at hwcan
  exact hwcan

/-- The same successful Pair active-body prefix supplies all three square-call
inputs. Starting only from canonicality of the selected `extra[side]` read,
canonicality of the repeated QM products and square outputs is derived from the
accepted concrete operations. The resulting three source-cut calls therefore
reuse the actual body values; no square-success premise is added. -/
theorem active_body_square_prefix_maps_to_source
    (ap0 ap1 : AspisR1S9PairCallerBodyPrefixV1.W)
    (extra : Array PairQ (2#usize))
    (side : Std.Usize)
    (iterNext : AspisR1S9PairCallerBodyPrefixV1.R)
    (weights : AspisR1S9PairCallerBodyPrefixV1.W)
    (flow : ControlFlow
      (AspisR1S9PairCallerBodyPrefixV1.R × AspisR1S9PairCallerBodyPrefixV1.W)
      AspisR1S9PairCallerBodyPrefixV1.W)
    (hbody : AspisR1S9PairCallerBodyPrefixV1.pairActiveBody
      ap0 ap1 extra side iterNext weights = .ok flow)
    (hextra : ∀ (j : Std.Usize) (x : PairQ),
      Array.index_usize extra j = .ok x →
      Sem.canonical (AspisR1S9PairCallerStepV1.toP6Q x)) :
    ∃ (q q1 q2 q3 q4 q41 q8 q16 : PairQ),
      Array.index_usize extra side = .ok q ∧
      AspisR1S9PairCallerStepV1.field.QM31.mul
        AspisR1S9PairCallerStepV1.field.QM31.ONE q = .ok q1 ∧
      AspisR1S9PairCallerStepV1.field.QM31.mul q1 q = .ok q2 ∧
      AspisR1S9PairCallerStepV1.field.QM31.mul q2 q = .ok q3 ∧
      Array.index_usize
        (Array.make 4#usize
          [AspisR1S9PairCallerStepV1.field.QM31.ONE, q1, q2, q3]) 2#usize = .ok q4 ∧
      AspisR1S9PairCallerStepV1.field.QM31.square q4 = .ok q41 ∧
      AspisR1S9PairCallerStepV1.field.QM31.square q41 = .ok q8 ∧
      AspisR1S9PairCallerStepV1.field.QM31.square q8 = .ok q16 ∧
      AspisR1S9SquareMulQMCutV1.field.QM31.square
        (AspisR1S9QMSquareHelperSourceBridgeV1.toCut
          (AspisR1S9PairCallerStepV1.toP6Q q4)) =
        .ok (AspisR1S9QMSquareHelperSourceBridgeV1.toCut
          (AspisR1S9PairCallerStepV1.toP6Q q41)) ∧
      AspisR1S9SquareMulQMCutV1.field.QM31.square
        (AspisR1S9QMSquareHelperSourceBridgeV1.toCut
          (AspisR1S9PairCallerStepV1.toP6Q q41)) =
        .ok (AspisR1S9QMSquareHelperSourceBridgeV1.toCut
          (AspisR1S9PairCallerStepV1.toP6Q q8)) ∧
      AspisR1S9SquareMulQMCutV1.field.QM31.square
        (AspisR1S9QMSquareHelperSourceBridgeV1.toCut
          (AspisR1S9PairCallerStepV1.toP6Q q8)) =
        .ok (AspisR1S9QMSquareHelperSourceBridgeV1.toCut
          (AspisR1S9PairCallerStepV1.toP6Q q16)) := by
  obtain ⟨q, q1, q2, q3, unusedQ4, q4, q41, q8, q12, q16, low,
      hq, hq1, hq2, hq3, hUnused, hq4, hq41, hq8, hq12, hq16,
      hlow, htail⟩ :=
    AspisR1S9PairCallerBodyPrefixV1.pair_active_prefix_from_success
      ap0 ap1 extra side iterNext weights flow hbody
  have hqcan : Sem.canonical (AspisR1S9PairCallerStepV1.toP6Q q) :=
    hextra side q hq
  have hone : Sem.canonical
      (AspisR1S9PairCallerStepV1.toP6Q
        AspisR1S9PairCallerStepV1.field.QM31.ONE) := by
    rw [pair_one_to_helper]
    exact Sem.one_canonical
  have hq1can := pair_mul_success_canonical
    AspisR1S9PairCallerStepV1.field.QM31.ONE q q1 hone hqcan hq1
  have hq2can := pair_mul_success_canonical q1 q q2 hq1can hqcan hq2
  have hq4eq : q4 = q2 := by
    have hread : Array.index_usize
        (Array.make 4#usize
          [AspisR1S9PairCallerStepV1.field.QM31.ONE, q1, q2, q3]) 2#usize = .ok q2 := by
      rfl
    exact Result.ok.inj (hq4.symm.trans hread)
  have hq4can : Sem.canonical (AspisR1S9PairCallerStepV1.toP6Q q4) := by
    rw [hq4eq]
    exact hq2can
  have hq41can := pair_square_success_canonical q4 q41 hq4can hq41
  have hq8can := pair_square_success_canonical q41 q8 hq41can hq8
  have hsq4 : @AspisR1S9HelperP6.FieldOps.qmSquare
      AspisR1S9ConcreteFieldOpsV1.concreteFieldOps
      (AspisR1S9PairCallerStepV1.toP6Q q4) =
      .ok (AspisR1S9PairCallerStepV1.toP6Q q41) := by
    have hmap := AspisR1S9PairCallerStepOperationBridgeV1.map_qm_square q4
    rw [hq41] at hmap
    change Result.ok (AspisR1S9PairCallerStepV1.toP6Q q41) = _ at hmap
    exact hmap.symm
  have hsq8 : @AspisR1S9HelperP6.FieldOps.qmSquare
      AspisR1S9ConcreteFieldOpsV1.concreteFieldOps
      (AspisR1S9PairCallerStepV1.toP6Q q41) =
      .ok (AspisR1S9PairCallerStepV1.toP6Q q8) := by
    have hmap := AspisR1S9PairCallerStepOperationBridgeV1.map_qm_square q41
    rw [hq8] at hmap
    change Result.ok (AspisR1S9PairCallerStepV1.toP6Q q8) = _ at hmap
    exact hmap.symm
  have hsq16 : @AspisR1S9HelperP6.FieldOps.qmSquare
      AspisR1S9ConcreteFieldOpsV1.concreteFieldOps
      (AspisR1S9PairCallerStepV1.toP6Q q8) =
      .ok (AspisR1S9PairCallerStepV1.toP6Q q16) := by
    have hmap := AspisR1S9PairCallerStepOperationBridgeV1.map_qm_square q8
    rw [hq16] at hmap
    change Result.ok (AspisR1S9PairCallerStepV1.toP6Q q16) = _ at hmap
    exact hmap.symm
  have hc1 := AspisR1S9QMSquarePrefixCutV1.source_square_same_success
    (AspisR1S9PairCallerStepV1.toP6Q q4)
    (AspisR1S9PairCallerStepV1.toP6Q q41) hq4can hsq4
  have hc2 := AspisR1S9QMSquarePrefixCutV1.source_square_same_success
    (AspisR1S9PairCallerStepV1.toP6Q q41)
    (AspisR1S9PairCallerStepV1.toP6Q q8) hq41can hsq8
  have hc3 := AspisR1S9QMSquarePrefixCutV1.source_square_same_success
    (AspisR1S9PairCallerStepV1.toP6Q q8)
    (AspisR1S9PairCallerStepV1.toP6Q q16) hq8can hsq16
  exact ⟨q, q1, q2, q3, q4, q41, q8, q16, hq, hq1, hq2, hq3, hq4, hq41,
    hq8, hq16, hc1, hc2, hc3⟩

/-- Lift the prefix statement to the exact generated body selected by the same
successful iterator `next`. -/
theorem source_body_square_prefix_maps_to_source
    (ap0 ap1 : AspisR1S9PairCallerBodyPrefixV1.W)
    (extra : Array PairQ (2#usize))
    (iter iterNext : AspisR1S9PairCallerBodyPrefixV1.R)
    (side : Std.Usize)
    (weights : AspisR1S9PairCallerBodyPrefixV1.W)
    (flow : ControlFlow
      (AspisR1S9PairCallerBodyPrefixV1.R × AspisR1S9PairCallerBodyPrefixV1.W)
      AspisR1S9PairCallerBodyPrefixV1.W)
    (hnext : core.iter.range.IteratorRange.next
      core.iter.range.StepUsize iter = .ok (some side, iterNext))
    (hbody : AspisR1S9PairCallerStepV1.weights.factored_s2_libra_weights_loop.body
      ap0 ap1 extra iter weights = .ok flow)
    (hextra : ∀ (j : Std.Usize) (x : PairQ),
      Array.index_usize extra j = .ok x →
      Sem.canonical (AspisR1S9PairCallerStepV1.toP6Q x)) :
    ∃ (q q1 q2 q3 q4 q41 q8 q16 : PairQ),
      Array.index_usize extra side = .ok q ∧
      AspisR1S9PairCallerStepV1.field.QM31.mul
        AspisR1S9PairCallerStepV1.field.QM31.ONE q = .ok q1 ∧
      AspisR1S9PairCallerStepV1.field.QM31.mul q1 q = .ok q2 ∧
      AspisR1S9PairCallerStepV1.field.QM31.mul q2 q = .ok q3 ∧
      Array.index_usize
        (Array.make 4#usize
          [AspisR1S9PairCallerStepV1.field.QM31.ONE, q1, q2, q3]) 2#usize = .ok q4 ∧
      AspisR1S9PairCallerStepV1.field.QM31.square q4 = .ok q41 ∧
      AspisR1S9PairCallerStepV1.field.QM31.square q41 = .ok q8 ∧
      AspisR1S9PairCallerStepV1.field.QM31.square q8 = .ok q16 ∧
      AspisR1S9SquareMulQMCutV1.field.QM31.square
        (AspisR1S9QMSquareHelperSourceBridgeV1.toCut
          (AspisR1S9PairCallerStepV1.toP6Q q4)) =
        .ok (AspisR1S9QMSquareHelperSourceBridgeV1.toCut
          (AspisR1S9PairCallerStepV1.toP6Q q41)) ∧
      AspisR1S9SquareMulQMCutV1.field.QM31.square
        (AspisR1S9QMSquareHelperSourceBridgeV1.toCut
          (AspisR1S9PairCallerStepV1.toP6Q q41)) =
        .ok (AspisR1S9QMSquareHelperSourceBridgeV1.toCut
          (AspisR1S9PairCallerStepV1.toP6Q q8)) ∧
      AspisR1S9SquareMulQMCutV1.field.QM31.square
        (AspisR1S9QMSquareHelperSourceBridgeV1.toCut
          (AspisR1S9PairCallerStepV1.toP6Q q8)) =
        .ok (AspisR1S9QMSquareHelperSourceBridgeV1.toCut
          (AspisR1S9PairCallerStepV1.toP6Q q16)) := by
  have hactive :=
    (AspisR1S9PairCallerBodyPrefixV1.body_some_eq_pairActiveBody
      ap0 ap1 extra iter iterNext side weights hnext).symm.trans hbody
  exact active_body_square_prefix_maps_to_source
    ap0 ap1 extra side iterNext weights flow hactive hextra

#print axioms active_body_square_prefix_maps_to_source
#print axioms source_body_square_prefix_maps_to_source

end AspisR1S9PairActiveSquarePrefixV1
