import S9CandidateFoldMapPrimitivesV1
import S9CandidateHelperOperationBridgeV1
import S9CandidateUpdateMapV1

set_option autoImplicit false
open Aeneas Aeneas.Std Result

namespace AspisR1S9CandidateSideOneTailMapV1

abbrev C := AspisR1S9CandidateHelperV1.field.WideExact
abbrev P := AspisR1S9HelperP6.field.WideExact
abbrev CQ := AspisR1S9CandidateHelperV1.field.QM31
abbrev PQ := AspisR1S9HelperP6.field.QM31
abbrev CA := Array C (4#usize)
abbrev PA := Array P (4#usize)

private theorem map_update_fixed {α β : Type} {n : Usize}
    (f : α → β) (a : Array α n) (i : Usize) (x : α) (hi : i.val < n.val) :
    AspisR1S9CandidateFoldMapPrimitivesV1.mapResult
      (AspisR1S9CandidateFoldMapPrimitivesV1.mapArray f)
      (Array.update a i x) =
    Array.update (AspisR1S9CandidateFoldMapPrimitivesV1.mapArray f a) i (f x) := by
  have hlen : i.val < a.length := by simpa [a.property] using hi
  obtain ⟨u, hu, _⟩ := WP.spec_imp_exists (Array.update_spec a i x hlen)
  obtain ⟨u', hu', hmap⟩ :=
    AspisR1S9CandidateUpdateMapV1.mapArray_update_success f a i x hi u hu
  rw [hu, hu']
  simp only [AspisR1S9CandidateFoldMapPrimitivesV1.mapResult]
  exact congrArg Result.ok hmap

/-- Maps the final actual wide-by-QM product and fixed slot-3 write as one
full Result computation. -/
theorem map_qmwide_update3 (weights2 : CA) (we11 : C) (q3 : CQ) :
    AspisR1S9CandidateFoldMapPrimitivesV1.mapResult
      (AspisR1S9CandidateFoldMapPrimitivesV1.mapArray
        AspisR1S9CandidateHelperV1.toP6W)
      (do
        let we12 ← AspisR1S9CandidateHelperV1.field.WideExact.mul_qm31 we11 q3
        Array.update weights2 3#usize we12) =
    (do
      let we12 ← @AspisR1S9HelperP6.FieldOps.wideMulQM31
        AspisR1S9ConcreteFieldOpsV1.concreteFieldOps
        (AspisR1S9CandidateHelperV1.toP6W we11)
        (AspisR1S9CandidateHelperV1.toP6Q q3)
      Array.update
        (AspisR1S9CandidateFoldMapPrimitivesV1.mapArray
          AspisR1S9CandidateHelperV1.toP6W weights2) 3#usize we12) := by
  apply AspisR1S9CandidateFoldMapPrimitivesV1.mapResult_bind_congr
    (AspisR1S9CandidateFoldMapPrimitivesV1.mapArray
      AspisR1S9CandidateHelperV1.toP6W)
    AspisR1S9CandidateHelperV1.toP6W
    (AspisR1S9CandidateHelperV1.field.WideExact.mul_qm31 we11 q3)
    (@AspisR1S9HelperP6.FieldOps.wideMulQM31
      AspisR1S9ConcreteFieldOpsV1.concreteFieldOps
      (AspisR1S9CandidateHelperV1.toP6W we11)
      (AspisR1S9CandidateHelperV1.toP6Q q3))
    (fun we12 => Array.update weights2 3#usize we12)
    (fun we12 => Array.update
      (AspisR1S9CandidateFoldMapPrimitivesV1.mapArray
        AspisR1S9CandidateHelperV1.toP6W weights2) 3#usize we12)
    (AspisR1S9CandidateHelperBridgeV1.map_wide_mul_qm31 we11 q3)
    (by
      intro we12
      exact map_update_fixed AspisR1S9CandidateHelperV1.toP6W
        weights2 3#usize we12 (by decide))

/-- Adds the actual q16*q41 call immediately before the final term write,
preserving the same result carrier and all Result branches. -/
theorem map_qmMul_then_qmwide_update3
    (weights2 : CA) (we11 : C) (q16 q41 : CQ) :
    AspisR1S9CandidateFoldMapPrimitivesV1.mapResult
      (AspisR1S9CandidateFoldMapPrimitivesV1.mapArray
        AspisR1S9CandidateHelperV1.toP6W)
      (do
        let q3 ← AspisR1S9CandidateHelperV1.field.QM31.mul q16 q41
        let we12 ← AspisR1S9CandidateHelperV1.field.WideExact.mul_qm31 we11 q3
        Array.update weights2 3#usize we12) =
    (do
      let q3 ← @AspisR1S9HelperP6.FieldOps.qmMul
        AspisR1S9ConcreteFieldOpsV1.concreteFieldOps
        (AspisR1S9CandidateHelperV1.toP6Q q16)
        (AspisR1S9CandidateHelperV1.toP6Q q41)
      let we12 ← @AspisR1S9HelperP6.FieldOps.wideMulQM31
        AspisR1S9ConcreteFieldOpsV1.concreteFieldOps
        (AspisR1S9CandidateHelperV1.toP6W we11) q3
      Array.update
        (AspisR1S9CandidateFoldMapPrimitivesV1.mapArray
          AspisR1S9CandidateHelperV1.toP6W weights2) 3#usize we12) := by
  apply AspisR1S9CandidateFoldMapPrimitivesV1.mapResult_bind_congr
    (AspisR1S9CandidateFoldMapPrimitivesV1.mapArray
      AspisR1S9CandidateHelperV1.toP6W)
    AspisR1S9CandidateHelperV1.toP6Q
    (AspisR1S9CandidateHelperV1.field.QM31.mul q16 q41)
    (@AspisR1S9HelperP6.FieldOps.qmMul
      AspisR1S9ConcreteFieldOpsV1.concreteFieldOps
      (AspisR1S9CandidateHelperV1.toP6Q q16)
      (AspisR1S9CandidateHelperV1.toP6Q q41))
    (fun q3 => do
      let we12 ← AspisR1S9CandidateHelperV1.field.WideExact.mul_qm31 we11 q3
      Array.update weights2 3#usize we12)
    (fun q3 => do
      let we12 ← @AspisR1S9HelperP6.FieldOps.wideMulQM31
        AspisR1S9ConcreteFieldOpsV1.concreteFieldOps
        (AspisR1S9CandidateHelperV1.toP6W we11) q3
      Array.update
        (AspisR1S9CandidateFoldMapPrimitivesV1.mapArray
          AspisR1S9CandidateHelperV1.toP6W weights2) 3#usize we12)
    (AspisR1S9CandidateHelperBridgeV1.map_qm_mul q16 q41)
    (by
      intro q3
      exact map_qmwide_update3 weights2 we11 q3)

#print axioms map_qmwide_update3
#print axioms map_qmMul_then_qmwide_update3

end AspisR1S9CandidateSideOneTailMapV1

