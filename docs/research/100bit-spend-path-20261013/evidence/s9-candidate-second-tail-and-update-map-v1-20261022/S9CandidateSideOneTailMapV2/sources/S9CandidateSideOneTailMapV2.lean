import S9CandidateSideOneTailMapV1

set_option autoImplicit false
open Aeneas Aeneas.Std Result

namespace AspisR1S9CandidateSideOneTailMapV2

open AspisR1S9CandidateSideOneTailMapV1

abbrev C := AspisR1S9CandidateSideOneTailMapV1.C
abbrev CQ := AspisR1S9CandidateSideOneTailMapV1.CQ
abbrev CA := AspisR1S9CandidateSideOneTailMapV1.CA

private theorem map_update_fixed {α β : Type} {n : Usize}
    (f : α → β) (a : Array α n) (i : Usize) (x : α) (hi : i.val < n.val) :
    AspisR1S9CandidateFoldMapPrimitivesV1.mapResult
      (AspisR1S9CandidateFoldMapPrimitivesV1.mapArray f)
      (Array.update a i x) =
    Array.update
      (AspisR1S9CandidateFoldMapPrimitivesV1.mapArray f a) i (f x) := by
  have hlen : i.val < a.length := by simpa [a.property] using hi
  obtain ⟨u, hu, _⟩ := WP.spec_imp_exists (Array.update_spec a i x hlen)
  obtain ⟨u', hu', hmap⟩ :=
    AspisR1S9CandidateUpdateMapV1.mapArray_update_success f a i x hi u hu
  rw [hu, hu']
  simp only [AspisR1S9CandidateFoldMapPrimitivesV1.mapResult]
  exact congrArg Result.ok hmap

private theorem map_mul_first2_qm_tail
    (weights2 : CA) (low first2 : C) (q16 q41 : CQ) :
    AspisR1S9CandidateFoldMapPrimitivesV1.mapResult
      (AspisR1S9CandidateFoldMapPrimitivesV1.mapArray
        AspisR1S9CandidateHelperV1.toP6W)
      (do
        let we11 ← AspisR1S9CandidateHelperV1.field.WideExact.mul low first2
        let q3 ← AspisR1S9CandidateHelperV1.field.QM31.mul q16 q41
        let we12 ← AspisR1S9CandidateHelperV1.field.WideExact.mul_qm31 we11 q3
        Array.update weights2 3#usize we12) =
    (do
      let we11 ← @AspisR1S9HelperP6.FieldOps.wideMul
        AspisR1S9ConcreteFieldOpsV1.concreteFieldOps
        (AspisR1S9CandidateHelperV1.toP6W low)
        (AspisR1S9CandidateHelperV1.toP6W first2)
      let q3 ← @AspisR1S9HelperP6.FieldOps.qmMul
        AspisR1S9ConcreteFieldOpsV1.concreteFieldOps
        (AspisR1S9CandidateHelperV1.toP6Q q16)
        (AspisR1S9CandidateHelperV1.toP6Q q41)
      let we12 ← @AspisR1S9HelperP6.FieldOps.wideMulQM31
        AspisR1S9ConcreteFieldOpsV1.concreteFieldOps
        we11 q3
      Array.update
        (AspisR1S9CandidateFoldMapPrimitivesV1.mapArray
          AspisR1S9CandidateHelperV1.toP6W weights2) 3#usize we12) := by
  apply AspisR1S9CandidateFoldMapPrimitivesV1.mapResult_bind_congr
    (AspisR1S9CandidateFoldMapPrimitivesV1.mapArray
      AspisR1S9CandidateHelperV1.toP6W)
    AspisR1S9CandidateHelperV1.toP6W
    (AspisR1S9CandidateHelperV1.field.WideExact.mul low first2)
    (@AspisR1S9HelperP6.FieldOps.wideMul
      AspisR1S9ConcreteFieldOpsV1.concreteFieldOps
      (AspisR1S9CandidateHelperV1.toP6W low)
      (AspisR1S9CandidateHelperV1.toP6W first2))
    (fun we11 => do
      let q3 ← AspisR1S9CandidateHelperV1.field.QM31.mul q16 q41
      let we12 ← AspisR1S9CandidateHelperV1.field.WideExact.mul_qm31 we11 q3
      Array.update weights2 3#usize we12)
    (fun we11 => do
      let q3 ← @AspisR1S9HelperP6.FieldOps.qmMul
        AspisR1S9ConcreteFieldOpsV1.concreteFieldOps
        (AspisR1S9CandidateHelperV1.toP6Q q16)
        (AspisR1S9CandidateHelperV1.toP6Q q41)
      let we12 ← @AspisR1S9HelperP6.FieldOps.wideMulQM31
        AspisR1S9ConcreteFieldOpsV1.concreteFieldOps we11 q3
      Array.update
        (AspisR1S9CandidateFoldMapPrimitivesV1.mapArray
          AspisR1S9CandidateHelperV1.toP6W weights2) 3#usize we12)
    (AspisR1S9CandidateHelperBridgeV1.map_wide_mul low first2)
    (by intro we11; exact map_qmMul_then_qmwide_update3 weights2 we11 q16 q41)

private theorem map_update2_then_tail
    (weights1 : CA) (we10 : C) (low first2 : C) (q16 q41 : CQ) :
    AspisR1S9CandidateFoldMapPrimitivesV1.mapResult
      (AspisR1S9CandidateFoldMapPrimitivesV1.mapArray
        AspisR1S9CandidateHelperV1.toP6W)
      (do
        let weights2 ← Array.update weights1 2#usize we10
        let we11 ← AspisR1S9CandidateHelperV1.field.WideExact.mul low first2
        let q3 ← AspisR1S9CandidateHelperV1.field.QM31.mul q16 q41
        let we12 ← AspisR1S9CandidateHelperV1.field.WideExact.mul_qm31 we11 q3
        Array.update weights2 3#usize we12) =
    (do
      let weights2 ← Array.update
        (AspisR1S9CandidateFoldMapPrimitivesV1.mapArray
          AspisR1S9CandidateHelperV1.toP6W weights1) 2#usize
        (AspisR1S9CandidateHelperV1.toP6W we10)
      let we11 ← @AspisR1S9HelperP6.FieldOps.wideMul
        AspisR1S9ConcreteFieldOpsV1.concreteFieldOps
        (AspisR1S9CandidateHelperV1.toP6W low)
        (AspisR1S9CandidateHelperV1.toP6W first2)
      let q3 ← @AspisR1S9HelperP6.FieldOps.qmMul
        AspisR1S9ConcreteFieldOpsV1.concreteFieldOps
        (AspisR1S9CandidateHelperV1.toP6Q q16)
        (AspisR1S9CandidateHelperV1.toP6Q q41)
      let we12 ← @AspisR1S9HelperP6.FieldOps.wideMulQM31
        AspisR1S9ConcreteFieldOpsV1.concreteFieldOps we11 q3
      Array.update weights2 3#usize we12) := by
  apply AspisR1S9CandidateFoldMapPrimitivesV1.mapResult_bind_congr
    (AspisR1S9CandidateFoldMapPrimitivesV1.mapArray
      AspisR1S9CandidateHelperV1.toP6W)
    (AspisR1S9CandidateFoldMapPrimitivesV1.mapArray
      AspisR1S9CandidateHelperV1.toP6W)
    (Array.update weights1 2#usize we10)
    (Array.update
      (AspisR1S9CandidateFoldMapPrimitivesV1.mapArray
        AspisR1S9CandidateHelperV1.toP6W weights1) 2#usize
      (AspisR1S9CandidateHelperV1.toP6W we10))
    (fun weights2 => do
      let we11 ← AspisR1S9CandidateHelperV1.field.WideExact.mul low first2
      let q3 ← AspisR1S9CandidateHelperV1.field.QM31.mul q16 q41
      let we12 ← AspisR1S9CandidateHelperV1.field.WideExact.mul_qm31 we11 q3
      Array.update weights2 3#usize we12)
    (fun weights2 => do
      let we11 ← @AspisR1S9HelperP6.FieldOps.wideMul
        AspisR1S9ConcreteFieldOpsV1.concreteFieldOps
        (AspisR1S9CandidateHelperV1.toP6W low)
        (AspisR1S9CandidateHelperV1.toP6W first2)
      let q3 ← @AspisR1S9HelperP6.FieldOps.qmMul
        AspisR1S9ConcreteFieldOpsV1.concreteFieldOps
        (AspisR1S9CandidateHelperV1.toP6Q q16)
        (AspisR1S9CandidateHelperV1.toP6Q q41)
      let we12 ← @AspisR1S9HelperP6.FieldOps.wideMulQM31
        AspisR1S9ConcreteFieldOpsV1.concreteFieldOps we11 q3
      Array.update weights2 3#usize we12)
    (map_update_fixed AspisR1S9CandidateHelperV1.toP6W
      weights1 2#usize we10 (by decide))
    (by intro weights2; exact map_mul_first2_qm_tail weights2 low first2 q16 q41)

/-- Maps the q41-scaled all-term product and the subsequent slot-2 update,
then carries through the same first2 and q16*q41 suffix. -/
theorem map_mul_all_qm_update2_then_tail
    (weights1 : CA) (low all first2 : C) (q41 q16 : CQ) :
    AspisR1S9CandidateFoldMapPrimitivesV1.mapResult
      (AspisR1S9CandidateFoldMapPrimitivesV1.mapArray
        AspisR1S9CandidateHelperV1.toP6W)
      (do
        let we9 ← AspisR1S9CandidateHelperV1.field.WideExact.mul low all
        let we10 ← AspisR1S9CandidateHelperV1.field.WideExact.mul_qm31 we9 q41
        let weights2 ← Array.update weights1 2#usize we10
        let we11 ← AspisR1S9CandidateHelperV1.field.WideExact.mul low first2
        let q3 ← AspisR1S9CandidateHelperV1.field.QM31.mul q16 q41
        let we12 ← AspisR1S9CandidateHelperV1.field.WideExact.mul_qm31 we11 q3
        Array.update weights2 3#usize we12) =
    (do
      let we9 ← @AspisR1S9HelperP6.FieldOps.wideMul
        AspisR1S9ConcreteFieldOpsV1.concreteFieldOps
        (AspisR1S9CandidateHelperV1.toP6W low)
        (AspisR1S9CandidateHelperV1.toP6W all)
      let we10 ← @AspisR1S9HelperP6.FieldOps.wideMulQM31
        AspisR1S9ConcreteFieldOpsV1.concreteFieldOps we9
        (AspisR1S9CandidateHelperV1.toP6Q q41)
      let weights2 ← Array.update
        (AspisR1S9CandidateFoldMapPrimitivesV1.mapArray
          AspisR1S9CandidateHelperV1.toP6W weights1) 2#usize we10
      let we11 ← @AspisR1S9HelperP6.FieldOps.wideMul
        AspisR1S9ConcreteFieldOpsV1.concreteFieldOps
        (AspisR1S9CandidateHelperV1.toP6W low)
        (AspisR1S9CandidateHelperV1.toP6W first2)
      let q3 ← @AspisR1S9HelperP6.FieldOps.qmMul
        AspisR1S9ConcreteFieldOpsV1.concreteFieldOps
        (AspisR1S9CandidateHelperV1.toP6Q q16)
        (AspisR1S9CandidateHelperV1.toP6Q q41)
      let we12 ← @AspisR1S9HelperP6.FieldOps.wideMulQM31
        AspisR1S9ConcreteFieldOpsV1.concreteFieldOps we11 q3
      Array.update weights2 3#usize we12) := by
  apply AspisR1S9CandidateFoldMapPrimitivesV1.mapResult_bind_congr
    (AspisR1S9CandidateFoldMapPrimitivesV1.mapArray
      AspisR1S9CandidateHelperV1.toP6W)
    AspisR1S9CandidateHelperV1.toP6W
    (AspisR1S9CandidateHelperV1.field.WideExact.mul low all)
    (@AspisR1S9HelperP6.FieldOps.wideMul
      AspisR1S9ConcreteFieldOpsV1.concreteFieldOps
      (AspisR1S9CandidateHelperV1.toP6W low)
      (AspisR1S9CandidateHelperV1.toP6W all))
    (fun we9 => do
      let we10 ← AspisR1S9CandidateHelperV1.field.WideExact.mul_qm31 we9 q41
      let weights2 ← Array.update weights1 2#usize we10
      let we11 ← AspisR1S9CandidateHelperV1.field.WideExact.mul low first2
      let q3 ← AspisR1S9CandidateHelperV1.field.QM31.mul q16 q41
      let we12 ← AspisR1S9CandidateHelperV1.field.WideExact.mul_qm31 we11 q3
      Array.update weights2 3#usize we12)
    (fun we9 => do
      let we10 ← @AspisR1S9HelperP6.FieldOps.wideMulQM31
        AspisR1S9ConcreteFieldOpsV1.concreteFieldOps we9
        (AspisR1S9CandidateHelperV1.toP6Q q41)
      let weights2 ← Array.update
        (AspisR1S9CandidateFoldMapPrimitivesV1.mapArray
          AspisR1S9CandidateHelperV1.toP6W weights1) 2#usize we10
      let we11 ← @AspisR1S9HelperP6.FieldOps.wideMul
        AspisR1S9ConcreteFieldOpsV1.concreteFieldOps
        (AspisR1S9CandidateHelperV1.toP6W low)
        (AspisR1S9CandidateHelperV1.toP6W first2)
      let q3 ← @AspisR1S9HelperP6.FieldOps.qmMul
        AspisR1S9ConcreteFieldOpsV1.concreteFieldOps
        (AspisR1S9CandidateHelperV1.toP6Q q16)
        (AspisR1S9CandidateHelperV1.toP6Q q41)
      let we12 ← @AspisR1S9HelperP6.FieldOps.wideMulQM31
        AspisR1S9ConcreteFieldOpsV1.concreteFieldOps we11 q3
      Array.update weights2 3#usize we12)
    (AspisR1S9CandidateHelperBridgeV1.map_wide_mul low all)
    (by
      intro we9
      apply AspisR1S9CandidateFoldMapPrimitivesV1.mapResult_bind_congr
        (AspisR1S9CandidateFoldMapPrimitivesV1.mapArray
          AspisR1S9CandidateHelperV1.toP6W)
        AspisR1S9CandidateHelperV1.toP6W
        (AspisR1S9CandidateHelperV1.field.WideExact.mul_qm31 we9 q41)
        (@AspisR1S9HelperP6.FieldOps.wideMulQM31
          AspisR1S9ConcreteFieldOpsV1.concreteFieldOps
          (AspisR1S9CandidateHelperV1.toP6W we9)
          (AspisR1S9CandidateHelperV1.toP6Q q41))
        (fun we10 => do
          let weights2 ← Array.update weights1 2#usize we10
          let we11 ← AspisR1S9CandidateHelperV1.field.WideExact.mul low first2
          let q3 ← AspisR1S9CandidateHelperV1.field.QM31.mul q16 q41
          let we12 ← AspisR1S9CandidateHelperV1.field.WideExact.mul_qm31 we11 q3
          Array.update weights2 3#usize we12)
        (fun we10 => do
          let weights2 ← Array.update
            (AspisR1S9CandidateFoldMapPrimitivesV1.mapArray
              AspisR1S9CandidateHelperV1.toP6W weights1) 2#usize we10
          let we11 ← @AspisR1S9HelperP6.FieldOps.wideMul
            AspisR1S9ConcreteFieldOpsV1.concreteFieldOps
            (AspisR1S9CandidateHelperV1.toP6W low)
            (AspisR1S9CandidateHelperV1.toP6W first2)
          let q3 ← @AspisR1S9HelperP6.FieldOps.qmMul
            AspisR1S9ConcreteFieldOpsV1.concreteFieldOps
            (AspisR1S9CandidateHelperV1.toP6Q q16)
            (AspisR1S9CandidateHelperV1.toP6Q q41)
          let we12 ← @AspisR1S9HelperP6.FieldOps.wideMulQM31
            AspisR1S9ConcreteFieldOpsV1.concreteFieldOps we11 q3
          Array.update weights2 3#usize we12)
        (AspisR1S9CandidateHelperBridgeV1.map_wide_mul_qm31 we9 q41)
        (by
          intro we10
          exact map_update2_then_tail weights1 we10 low first2 q16 q41))

#print axioms map_mul_all_qm_update2_then_tail

end AspisR1S9CandidateSideOneTailMapV2

