import S9CandidateSideOneTailMapV3
import S9CandidatePerm3BridgeV1

set_option autoImplicit false
open Aeneas Aeneas.Std Result

namespace AspisR1S9CandidateSideOneTailMapV4

abbrev C := AspisR1S9CandidateSideOneTailMapV1.C
abbrev CQ := AspisR1S9CandidateSideOneTailMapV1.CQ
abbrev CA := AspisR1S9CandidateSideOneTailMapV1.CA
abbrev P := AspisR1S9CandidateSideOneTailMapV1.P
abbrev PQ := AspisR1S9CandidateSideOneTailMapV1.PQ
abbrev PA := AspisR1S9CandidateSideOneTailMapV1.PA
abbrev U := Std.Usize

def candidateAddTail
    (old : CA) (we4 we7 low all first2 : C) (q41 q16 : CQ) : Result CA := do
  let we8 ← AspisR1S9CandidateHelperV1.field.WideExact.add we4 we7
  let weights1 ← Array.update old 1#usize we8
  let we9 ← AspisR1S9CandidateHelperV1.field.WideExact.mul low all
  let we10 ← AspisR1S9CandidateHelperV1.field.WideExact.mul_qm31 we9 q41
  let weights2 ← Array.update weights1 2#usize we10
  let we11 ← AspisR1S9CandidateHelperV1.field.WideExact.mul low first2
  let q3 ← AspisR1S9CandidateHelperV1.field.QM31.mul q16 q41
  let we12 ← AspisR1S9CandidateHelperV1.field.WideExact.mul_qm31 we11 q3
  Array.update weights2 3#usize we12

def p6AddTail
    (old : PA) (we4 we7 low all first2 : P) (q41 q16 : PQ) : Result PA := do
  let we8 ← @AspisR1S9HelperP6.FieldOps.wideAdd
    AspisR1S9ConcreteFieldOpsV1.concreteFieldOps we4 we7
  let weights1 ← Array.update old 1#usize we8
  let we9 ← @AspisR1S9HelperP6.FieldOps.wideMul
    AspisR1S9ConcreteFieldOpsV1.concreteFieldOps low all
  let we10 ← @AspisR1S9HelperP6.FieldOps.wideMulQM31
    AspisR1S9ConcreteFieldOpsV1.concreteFieldOps we9 q41
  let weights2 ← Array.update weights1 2#usize we10
  let we11 ← @AspisR1S9HelperP6.FieldOps.wideMul
    AspisR1S9ConcreteFieldOpsV1.concreteFieldOps low first2
  let q3 ← @AspisR1S9HelperP6.FieldOps.qmMul
    AspisR1S9ConcreteFieldOpsV1.concreteFieldOps q16 q41
  let we12 ← @AspisR1S9HelperP6.FieldOps.wideMulQM31
    AspisR1S9ConcreteFieldOpsV1.concreteFieldOps we11 q3
  Array.update weights2 3#usize we12

theorem map_add_tail
    (old : CA) (we4 we7 low all first2 : C) (q41 q16 : CQ) :
    AspisR1S9CandidateFoldMapPrimitivesV1.mapResult
      (AspisR1S9CandidateFoldMapPrimitivesV1.mapArray
        AspisR1S9CandidateHelperV1.toP6W)
      (candidateAddTail old we4 we7 low all first2 q41 q16) =
    p6AddTail
      (AspisR1S9CandidateFoldMapPrimitivesV1.mapArray
        AspisR1S9CandidateHelperV1.toP6W old)
      (AspisR1S9CandidateHelperV1.toP6W we4)
      (AspisR1S9CandidateHelperV1.toP6W we7)
      (AspisR1S9CandidateHelperV1.toP6W low)
      (AspisR1S9CandidateHelperV1.toP6W all)
      (AspisR1S9CandidateHelperV1.toP6W first2)
      (AspisR1S9CandidateHelperV1.toP6Q q41)
      (AspisR1S9CandidateHelperV1.toP6Q q16) := by
  change
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
        Array.update weights2 3#usize we12) = _
  exact AspisR1S9CandidateSideOneTailMapV3.map_add_update1_all_tail
    old we4 we7 low all first2 q41 q16

theorem map_after_old_read
    (old : CA) (we4 : C) (ap1 : CA) (low all first2 : C)
    (q41 q16 : CQ) (perm3 : U) :
    AspisR1S9CandidateFoldMapPrimitivesV1.mapResult
      (AspisR1S9CandidateFoldMapPrimitivesV1.mapArray
        AspisR1S9CandidateHelperV1.toP6W)
      (do
        let we5 ← Array.index_usize ap1 perm3
        let we6 ← AspisR1S9CandidateHelperV1.field.WideExact.mul_m31 we5
          _root_.AspisR1S9CandidateHelperV1.weights.QUARTER
        let we7 ← AspisR1S9CandidateHelperV1.field.WideExact.mul low we6
        candidateAddTail old we4 we7 low all first2 q41 q16) =
    (do
      let we5 ← Array.index_usize
        (AspisR1S9CandidateFoldMapPrimitivesV1.mapArray
          AspisR1S9CandidateHelperV1.toP6W ap1) perm3
      let we6 ← @AspisR1S9HelperP6.FieldOps.wideMulM31
        AspisR1S9ConcreteFieldOpsV1.concreteFieldOps we5
        _root_.AspisR1S9HelperP6.weights.QUARTER
      let we7 ← @AspisR1S9HelperP6.FieldOps.wideMul
        AspisR1S9ConcreteFieldOpsV1.concreteFieldOps
        (AspisR1S9CandidateHelperV1.toP6W low) we6
      p6AddTail
        (AspisR1S9CandidateFoldMapPrimitivesV1.mapArray
          AspisR1S9CandidateHelperV1.toP6W old)
        (AspisR1S9CandidateHelperV1.toP6W we4) we7
        (AspisR1S9CandidateHelperV1.toP6W low)
        (AspisR1S9CandidateHelperV1.toP6W all)
        (AspisR1S9CandidateHelperV1.toP6W first2)
        (AspisR1S9CandidateHelperV1.toP6Q q41)
        (AspisR1S9CandidateHelperV1.toP6Q q16)) := by
  apply AspisR1S9CandidateFoldMapPrimitivesV1.mapResult_bind_congr
    (AspisR1S9CandidateFoldMapPrimitivesV1.mapArray
      AspisR1S9CandidateHelperV1.toP6W)
    AspisR1S9CandidateHelperV1.toP6W
    (Array.index_usize ap1 perm3)
    (Array.index_usize
      (AspisR1S9CandidateFoldMapPrimitivesV1.mapArray
        AspisR1S9CandidateHelperV1.toP6W ap1) perm3)
    (fun we5 => do
      let we6 ← AspisR1S9CandidateHelperV1.field.WideExact.mul_m31 we5
        _root_.AspisR1S9CandidateHelperV1.weights.QUARTER
      let we7 ← AspisR1S9CandidateHelperV1.field.WideExact.mul low we6
      candidateAddTail old we4 we7 low all first2 q41 q16)
    (fun we5 => do
      let we6 ← @AspisR1S9HelperP6.FieldOps.wideMulM31
        AspisR1S9ConcreteFieldOpsV1.concreteFieldOps we5
        _root_.AspisR1S9HelperP6.weights.QUARTER
      let we7 ← @AspisR1S9HelperP6.FieldOps.wideMul
        AspisR1S9ConcreteFieldOpsV1.concreteFieldOps
        (AspisR1S9CandidateHelperV1.toP6W low) we6
      p6AddTail
        (AspisR1S9CandidateFoldMapPrimitivesV1.mapArray
          AspisR1S9CandidateHelperV1.toP6W old)
        (AspisR1S9CandidateHelperV1.toP6W we4) we7
        (AspisR1S9CandidateHelperV1.toP6W low)
        (AspisR1S9CandidateHelperV1.toP6W all)
        (AspisR1S9CandidateHelperV1.toP6W first2)
        (AspisR1S9CandidateHelperV1.toP6Q q41)
        (AspisR1S9CandidateHelperV1.toP6Q q16))
    (AspisR1S9CandidateFoldMapPrimitivesV1.mapArray_index_result
      AspisR1S9CandidateHelperV1.toP6W ap1 perm3)
    (by
      intro we5
      apply AspisR1S9CandidateFoldMapPrimitivesV1.mapResult_bind_congr
        (AspisR1S9CandidateFoldMapPrimitivesV1.mapArray
          AspisR1S9CandidateHelperV1.toP6W)
        AspisR1S9CandidateHelperV1.toP6W
        (AspisR1S9CandidateHelperV1.field.WideExact.mul_m31 we5
          _root_.AspisR1S9CandidateHelperV1.weights.QUARTER)
        (@AspisR1S9HelperP6.FieldOps.wideMulM31
          AspisR1S9ConcreteFieldOpsV1.concreteFieldOps
          (AspisR1S9CandidateHelperV1.toP6W we5)
          _root_.AspisR1S9HelperP6.weights.QUARTER)
        (fun we6 => do
          let we7 ← AspisR1S9CandidateHelperV1.field.WideExact.mul low we6
          candidateAddTail old we4 we7 low all first2 q41 q16)
        (fun we6 => do
          let we7 ← @AspisR1S9HelperP6.FieldOps.wideMul
            AspisR1S9ConcreteFieldOpsV1.concreteFieldOps
            (AspisR1S9CandidateHelperV1.toP6W low) we6
          p6AddTail
            (AspisR1S9CandidateFoldMapPrimitivesV1.mapArray
              AspisR1S9CandidateHelperV1.toP6W old)
            (AspisR1S9CandidateHelperV1.toP6W we4) we7
            (AspisR1S9CandidateHelperV1.toP6W low)
            (AspisR1S9CandidateHelperV1.toP6W all)
            (AspisR1S9CandidateHelperV1.toP6W first2)
            (AspisR1S9CandidateHelperV1.toP6Q q41)
            (AspisR1S9CandidateHelperV1.toP6Q q16))
        (by
          have hquarter : AspisR1S9CandidateHelperV1.toP6M
              _root_.AspisR1S9CandidateHelperV1.weights.QUARTER =
              _root_.AspisR1S9HelperP6.weights.QUARTER := by
            unfold AspisR1S9CandidateHelperV1.weights.QUARTER
              AspisR1S9HelperP6.weights.QUARTER AspisR1S9CandidateHelperV1.toP6M
            rfl
          have hm := AspisR1S9CandidateHelperBridgeV1.map_wide_mul_m31 we5
            _root_.AspisR1S9CandidateHelperV1.weights.QUARTER
          change AspisR1S9CandidateHelperBridgeV1.mapResult AspisR1S9CandidateHelperV1.toP6W
            (AspisR1S9CandidateHelperV1.field.WideExact.mul_m31 we5
              _root_.AspisR1S9CandidateHelperV1.weights.QUARTER) = _
          rw [← hquarter]
          exact hm)
        (by
          intro we6
          apply AspisR1S9CandidateFoldMapPrimitivesV1.mapResult_bind_congr
            (AspisR1S9CandidateFoldMapPrimitivesV1.mapArray
              AspisR1S9CandidateHelperV1.toP6W)
            AspisR1S9CandidateHelperV1.toP6W
            (AspisR1S9CandidateHelperV1.field.WideExact.mul low we6)
            (@AspisR1S9HelperP6.FieldOps.wideMul
              AspisR1S9ConcreteFieldOpsV1.concreteFieldOps
              (AspisR1S9CandidateHelperV1.toP6W low)
              (AspisR1S9CandidateHelperV1.toP6W we6))
            (fun we7 => candidateAddTail old we4 we7 low all first2 q41 q16)
            (fun we7 => p6AddTail
              (AspisR1S9CandidateFoldMapPrimitivesV1.mapArray
                AspisR1S9CandidateHelperV1.toP6W old)
              (AspisR1S9CandidateHelperV1.toP6W we4) we7
              (AspisR1S9CandidateHelperV1.toP6W low)
              (AspisR1S9CandidateHelperV1.toP6W all)
              (AspisR1S9CandidateHelperV1.toP6W first2)
              (AspisR1S9CandidateHelperV1.toP6Q q41)
              (AspisR1S9CandidateHelperV1.toP6Q q16))
            (AspisR1S9CandidateHelperBridgeV1.map_wide_mul low we6)
            (by intro we7; exact map_add_tail old we4 we7 low all first2 q41 q16)))

def candidateAfterOld
    (old ap1 : CA) (low all first2 : C) (q41 q16 : CQ) (perm3 : U) : Result CA := do
  let we4 ← Array.index_usize old 1#usize
  let we5 ← Array.index_usize ap1 perm3
  let we6 ← AspisR1S9CandidateHelperV1.field.WideExact.mul_m31 we5
    _root_.AspisR1S9CandidateHelperV1.weights.QUARTER
  let we7 ← AspisR1S9CandidateHelperV1.field.WideExact.mul low we6
  candidateAddTail old we4 we7 low all first2 q41 q16

def p6AfterOld
    (old ap1 : PA) (low all first2 : P) (q41 q16 : PQ) : Result PA := do
  let we4 ← Array.index_usize old 1#usize
  let perm3 ← Array.index_usize _root_.AspisR1S9HelperP6.weights.PERM 3#usize
  let we5 ← Array.index_usize ap1 perm3
  let we6 ← @AspisR1S9HelperP6.FieldOps.wideMulM31
    AspisR1S9ConcreteFieldOpsV1.concreteFieldOps we5
    _root_.AspisR1S9HelperP6.weights.QUARTER
  let we7 ← @AspisR1S9HelperP6.FieldOps.wideMul
    AspisR1S9ConcreteFieldOpsV1.concreteFieldOps low we6
  p6AddTail old we4 we7 low all first2 q41 q16

/-- The full selected side-one fragment keeps the source's read order:
original slot-1 read, then the previously bound candidate PERM[3] value,
then ap1 scaling and the updates. The P6-side PERM[3] read is explicitly
transported from the same candidate read. -/
theorem candidate_side_one_from_bound_perm
    (old ap1 : CA) (low all first2 : C) (q41 q16 : CQ)
    (perm3 : U)
    (hperm3 : Array.index_usize
      _root_.AspisR1S9CandidateHelperV1.weights.PERM 3#usize = .ok perm3) :
    Array.index_usize
      _root_.AspisR1S9HelperP6.weights.PERM 3#usize = .ok perm3 ∧
    AspisR1S9CandidateFoldMapPrimitivesV1.mapResult
      (AspisR1S9CandidateFoldMapPrimitivesV1.mapArray
        AspisR1S9CandidateHelperV1.toP6W)
      (candidateAfterOld old ap1 low all first2 q41 q16 perm3) =
    p6AfterOld
      (AspisR1S9CandidateFoldMapPrimitivesV1.mapArray
        AspisR1S9CandidateHelperV1.toP6W old)
      (AspisR1S9CandidateFoldMapPrimitivesV1.mapArray
        AspisR1S9CandidateHelperV1.toP6W ap1)
      (AspisR1S9CandidateHelperV1.toP6W low)
      (AspisR1S9CandidateHelperV1.toP6W all)
      (AspisR1S9CandidateHelperV1.toP6W first2)
      (AspisR1S9CandidateHelperV1.toP6Q q41)
      (AspisR1S9CandidateHelperV1.toP6Q q16) := by
  have hperm3P6 :=
    AspisR1S9CandidatePerm3BridgeV1.candidate_perm3_read_transports perm3 hperm3
  constructor
  · exact hperm3P6
  · unfold candidateAfterOld p6AfterOld
    apply AspisR1S9CandidateFoldMapPrimitivesV1.mapResult_bind_congr
      (AspisR1S9CandidateFoldMapPrimitivesV1.mapArray
        AspisR1S9CandidateHelperV1.toP6W)
      AspisR1S9CandidateHelperV1.toP6W
      (Array.index_usize old 1#usize)
      (Array.index_usize
        (AspisR1S9CandidateFoldMapPrimitivesV1.mapArray
          AspisR1S9CandidateHelperV1.toP6W old) 1#usize)
      (fun we4 => do
        let we5 ← Array.index_usize ap1 perm3
        let we6 ← AspisR1S9CandidateHelperV1.field.WideExact.mul_m31 we5
          _root_.AspisR1S9CandidateHelperV1.weights.QUARTER
        let we7 ← AspisR1S9CandidateHelperV1.field.WideExact.mul low we6
        candidateAddTail old we4 we7 low all first2 q41 q16)
      (fun we4 => do
        let perm3 ← Array.index_usize _root_.AspisR1S9HelperP6.weights.PERM 3#usize
        let we5 ← Array.index_usize
          (AspisR1S9CandidateFoldMapPrimitivesV1.mapArray
            AspisR1S9CandidateHelperV1.toP6W ap1) perm3
        let we6 ← @AspisR1S9HelperP6.FieldOps.wideMulM31
          AspisR1S9ConcreteFieldOpsV1.concreteFieldOps we5
          _root_.AspisR1S9HelperP6.weights.QUARTER
        let we7 ← @AspisR1S9HelperP6.FieldOps.wideMul
          AspisR1S9ConcreteFieldOpsV1.concreteFieldOps
          (AspisR1S9CandidateHelperV1.toP6W low) we6
        p6AddTail
          (AspisR1S9CandidateFoldMapPrimitivesV1.mapArray
            AspisR1S9CandidateHelperV1.toP6W old)
          we4 we7
          (AspisR1S9CandidateHelperV1.toP6W low)
          (AspisR1S9CandidateHelperV1.toP6W all)
          (AspisR1S9CandidateHelperV1.toP6W first2)
          (AspisR1S9CandidateHelperV1.toP6Q q41)
          (AspisR1S9CandidateHelperV1.toP6Q q16))
      (AspisR1S9CandidateFoldMapPrimitivesV1.mapArray_index_result
        AspisR1S9CandidateHelperV1.toP6W old 1#usize)
      (by
        intro we4
        simpa [hperm3P6] using
          map_after_old_read old we4 ap1 low all first2 q41 q16 perm3)

#print axioms candidate_side_one_from_bound_perm

end AspisR1S9CandidateSideOneTailMapV4
