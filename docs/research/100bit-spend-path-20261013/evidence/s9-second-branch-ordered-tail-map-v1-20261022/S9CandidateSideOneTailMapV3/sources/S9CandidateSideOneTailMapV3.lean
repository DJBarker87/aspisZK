import S9CandidateSideOneTailMapV2
import S9CandidatePerm3BridgeV1
import S9SideOneTailRootV1
import S9CandidateUpdateResultMapV1

set_option autoImplicit false
open Aeneas Aeneas.Std Result

namespace AspisR1S9CandidateSideOneTailMapV3

open AspisR1S9CandidateSideOneTailMapV1
open AspisR1S9CandidateSideOneTailMapV2

abbrev C := AspisR1S9CandidateSideOneTailMapV1.C
abbrev CQ := AspisR1S9CandidateSideOneTailMapV1.CQ
abbrev CA := AspisR1S9CandidateSideOneTailMapV1.CA
abbrev PA := AspisR1S9CandidateSideOneTailMapV1.PA

theorem map_add_update1_all_tail
    (old : CA) (we4 we7 : C) (low all first2 : C) (q41 q16 : CQ) :
    AspisR1S9CandidateFoldMapPrimitivesV1.mapResult
      (AspisR1S9CandidateFoldMapPrimitivesV1.mapArray
        AspisR1S9CandidateHelperV1.toP6W)
      (do
        let we8 ← AspisR1S9CandidateHelperV1.field.WideExact.add we4 we7
        let weights1 ← Array.update old 1#usize we8
        let we9 ← AspisR1S9CandidateHelperV1.field.WideExact.mul low all
        let we10 ← AspisR1S9CandidateHelperV1.field.WideExact.mul_qm31 we9 q41
        let weights2 ← Array.update weights1 2#usize we10
        let we11 ← AspisR1S9CandidateHelperV1.field.WideExact.mul low first2
        let q3 ← AspisR1S9CandidateHelperV1.field.QM31.mul q16 q41
        let we12 ← AspisR1S9CandidateHelperV1.field.WideExact.mul_qm31 we11 q3
        Array.update weights2 3#usize we12) =
    (do
      let we8 ← @AspisR1S9HelperP6.FieldOps.wideAdd
        AspisR1S9ConcreteFieldOpsV1.concreteFieldOps
        (AspisR1S9CandidateHelperV1.toP6W we4)
        (AspisR1S9CandidateHelperV1.toP6W we7)
      let weights1 ← Array.update
        (AspisR1S9CandidateFoldMapPrimitivesV1.mapArray
          AspisR1S9CandidateHelperV1.toP6W old) 1#usize we8
      let we9 ← @AspisR1S9HelperP6.FieldOps.wideMul
        AspisR1S9ConcreteFieldOpsV1.concreteFieldOps
        (AspisR1S9CandidateHelperV1.toP6W low)
        (AspisR1S9CandidateHelperV1.toP6W all)
      let we10 ← @AspisR1S9HelperP6.FieldOps.wideMulQM31
        AspisR1S9ConcreteFieldOpsV1.concreteFieldOps we9
        (AspisR1S9CandidateHelperV1.toP6Q q41)
      let weights2 ← Array.update weights1 2#usize we10
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
    (AspisR1S9CandidateHelperV1.field.WideExact.add we4 we7)
    (@AspisR1S9HelperP6.FieldOps.wideAdd
      AspisR1S9ConcreteFieldOpsV1.concreteFieldOps
      (AspisR1S9CandidateHelperV1.toP6W we4)
      (AspisR1S9CandidateHelperV1.toP6W we7))
    (fun we8 => do
      let weights1 ← Array.update old 1#usize we8
      let we9 ← AspisR1S9CandidateHelperV1.field.WideExact.mul low all
      let we10 ← AspisR1S9CandidateHelperV1.field.WideExact.mul_qm31 we9 q41
      let weights2 ← Array.update weights1 2#usize we10
      let we11 ← AspisR1S9CandidateHelperV1.field.WideExact.mul low first2
      let q3 ← AspisR1S9CandidateHelperV1.field.QM31.mul q16 q41
      let we12 ← AspisR1S9CandidateHelperV1.field.WideExact.mul_qm31 we11 q3
      Array.update weights2 3#usize we12)
    (fun we8 => do
      let weights1 ← Array.update
        (AspisR1S9CandidateFoldMapPrimitivesV1.mapArray
          AspisR1S9CandidateHelperV1.toP6W old) 1#usize we8
      let we9 ← @AspisR1S9HelperP6.FieldOps.wideMul
        AspisR1S9ConcreteFieldOpsV1.concreteFieldOps
        (AspisR1S9CandidateHelperV1.toP6W low)
        (AspisR1S9CandidateHelperV1.toP6W all)
      let we10 ← @AspisR1S9HelperP6.FieldOps.wideMulQM31
        AspisR1S9ConcreteFieldOpsV1.concreteFieldOps we9
        (AspisR1S9CandidateHelperV1.toP6Q q41)
      let weights2 ← Array.update weights1 2#usize we10
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
    (AspisR1S9CandidateHelperBridgeV1.map_wide_add we4 we7)
    (by
      intro we8
      apply AspisR1S9CandidateFoldMapPrimitivesV1.mapResult_bind_congr
        (AspisR1S9CandidateFoldMapPrimitivesV1.mapArray
          AspisR1S9CandidateHelperV1.toP6W)
        (AspisR1S9CandidateFoldMapPrimitivesV1.mapArray
          AspisR1S9CandidateHelperV1.toP6W)
        (Array.update old 1#usize we8)
        (Array.update
          (AspisR1S9CandidateFoldMapPrimitivesV1.mapArray
            AspisR1S9CandidateHelperV1.toP6W old) 1#usize
          (AspisR1S9CandidateHelperV1.toP6W we8))
        (fun weights1 => do
          let we9 ← AspisR1S9CandidateHelperV1.field.WideExact.mul low all
          let we10 ← AspisR1S9CandidateHelperV1.field.WideExact.mul_qm31 we9 q41
          let weights2 ← Array.update weights1 2#usize we10
          let we11 ← AspisR1S9CandidateHelperV1.field.WideExact.mul low first2
          let q3 ← AspisR1S9CandidateHelperV1.field.QM31.mul q16 q41
          let we12 ← AspisR1S9CandidateHelperV1.field.WideExact.mul_qm31 we11 q3
          Array.update weights2 3#usize we12)
        (fun weights1 => do
          let we9 ← @AspisR1S9HelperP6.FieldOps.wideMul
            AspisR1S9ConcreteFieldOpsV1.concreteFieldOps
            (AspisR1S9CandidateHelperV1.toP6W low)
            (AspisR1S9CandidateHelperV1.toP6W all)
          let we10 ← @AspisR1S9HelperP6.FieldOps.wideMulQM31
            AspisR1S9ConcreteFieldOpsV1.concreteFieldOps we9
            (AspisR1S9CandidateHelperV1.toP6Q q41)
          let weights2 ← Array.update weights1 2#usize we10
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
        (AspisR1S9CandidateUpdateResultMapV1.mapArray_update_result
          AspisR1S9CandidateHelperV1.toP6W old 1#usize we8 (by decide))
        (by
          intro weights1
          exact AspisR1S9CandidateSideOneTailMapV2.map_mul_all_qm_update2_then_tail
            weights1 low all first2 q41 q16))

#print axioms map_add_update1_all_tail

end AspisR1S9CandidateSideOneTailMapV3

