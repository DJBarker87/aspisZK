import S9CandidateFoldMapPrimitivesV1
import S9CandidateHelperOperationBridgeV1
import S9SideZeroTailRootV1
import S9CandidateUpdateMapV1

set_option autoImplicit false
open Aeneas Aeneas.Std Result

namespace AspisR1S9CandidateSideZeroTailMapV1

abbrev C := AspisR1S9CandidateHelperV1.field.WideExact
abbrev P := AspisR1S9HelperP6.field.WideExact
abbrev CQ := AspisR1S9CandidateHelperV1.field.QM31
abbrev CA := Array C (4#usize)
abbrev PA := Array P (4#usize)

/-- Exact candidate source branch after the four terms have been summed. -/
def candidateSideZeroTail (old : CA) (low first3 all : C) (q16 : CQ) : Result CA := do
  let we12 ← AspisR1S9CandidateHelperV1.field.WideExact.mul low all
  let weights1 ← Array.update old 0#usize we12
  let we13 ← AspisR1S9CandidateHelperV1.field.WideExact.mul low first3
  let we14 ← AspisR1S9CandidateHelperV1.field.WideExact.mul_qm31 we13 q16
  Array.update weights1 1#usize we14

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

private theorem map_mul_qm_update (weights1 : CA) (we13 : C) (q16 : CQ) :
    AspisR1S9CandidateFoldMapPrimitivesV1.mapResult
      (AspisR1S9CandidateFoldMapPrimitivesV1.mapArray
        AspisR1S9CandidateHelperV1.toP6W)
      (do
        let we14 ← AspisR1S9CandidateHelperV1.field.WideExact.mul_qm31 we13 q16
        Array.update weights1 1#usize we14) =
    (do
      let we14 ← @AspisR1S9HelperP6.FieldOps.wideMulQM31
        AspisR1S9ConcreteFieldOpsV1.concreteFieldOps
        (AspisR1S9CandidateHelperV1.toP6W we13)
        (AspisR1S9CandidateHelperV1.toP6Q q16)
      Array.update
        (AspisR1S9CandidateFoldMapPrimitivesV1.mapArray
          AspisR1S9CandidateHelperV1.toP6W weights1) 1#usize we14) := by
  apply AspisR1S9CandidateFoldMapPrimitivesV1.mapResult_bind_congr
    (AspisR1S9CandidateFoldMapPrimitivesV1.mapArray
      AspisR1S9CandidateHelperV1.toP6W)
    AspisR1S9CandidateHelperV1.toP6W
    (AspisR1S9CandidateHelperV1.field.WideExact.mul_qm31 we13 q16)
    (@AspisR1S9HelperP6.FieldOps.wideMulQM31
      AspisR1S9ConcreteFieldOpsV1.concreteFieldOps
      (AspisR1S9CandidateHelperV1.toP6W we13)
      (AspisR1S9CandidateHelperV1.toP6Q q16))
    (fun we14 => Array.update weights1 1#usize we14)
    (fun we14 => Array.update
      (AspisR1S9CandidateFoldMapPrimitivesV1.mapArray
        AspisR1S9CandidateHelperV1.toP6W weights1) 1#usize we14)
    (AspisR1S9CandidateHelperBridgeV1.map_wide_mul_qm31 we13 q16)
    (by intro we14; exact map_update_fixed AspisR1S9CandidateHelperV1.toP6W weights1 1#usize we14 (by decide))

private theorem map_mul_first3_tail (weights1 : CA) (low first3 : C) (q16 : CQ) :
    AspisR1S9CandidateFoldMapPrimitivesV1.mapResult
      (AspisR1S9CandidateFoldMapPrimitivesV1.mapArray
        AspisR1S9CandidateHelperV1.toP6W)
      (do
        let we13 ← AspisR1S9CandidateHelperV1.field.WideExact.mul low first3
        let we14 ← AspisR1S9CandidateHelperV1.field.WideExact.mul_qm31 we13 q16
        Array.update weights1 1#usize we14) =
    (do
      let we13 ← @AspisR1S9HelperP6.FieldOps.wideMul
        AspisR1S9ConcreteFieldOpsV1.concreteFieldOps
        (AspisR1S9CandidateHelperV1.toP6W low)
        (AspisR1S9CandidateHelperV1.toP6W first3)
      let we14 ← @AspisR1S9HelperP6.FieldOps.wideMulQM31
        AspisR1S9ConcreteFieldOpsV1.concreteFieldOps
        we13 (AspisR1S9CandidateHelperV1.toP6Q q16)
      Array.update
        (AspisR1S9CandidateFoldMapPrimitivesV1.mapArray
          AspisR1S9CandidateHelperV1.toP6W weights1) 1#usize we14) := by
  apply AspisR1S9CandidateFoldMapPrimitivesV1.mapResult_bind_congr
    (AspisR1S9CandidateFoldMapPrimitivesV1.mapArray
      AspisR1S9CandidateHelperV1.toP6W)
    AspisR1S9CandidateHelperV1.toP6W
    (AspisR1S9CandidateHelperV1.field.WideExact.mul low first3)
    (@AspisR1S9HelperP6.FieldOps.wideMul
      AspisR1S9ConcreteFieldOpsV1.concreteFieldOps
      (AspisR1S9CandidateHelperV1.toP6W low)
      (AspisR1S9CandidateHelperV1.toP6W first3))
    (fun we13 => do
      let we14 ← AspisR1S9CandidateHelperV1.field.WideExact.mul_qm31 we13 q16
      Array.update weights1 1#usize we14)
    (fun we13 => do
      let we14 ← @AspisR1S9HelperP6.FieldOps.wideMulQM31
        AspisR1S9ConcreteFieldOpsV1.concreteFieldOps
        we13 (AspisR1S9CandidateHelperV1.toP6Q q16)
      Array.update
        (AspisR1S9CandidateFoldMapPrimitivesV1.mapArray
          AspisR1S9CandidateHelperV1.toP6W weights1) 1#usize we14)
    (AspisR1S9CandidateHelperBridgeV1.map_wide_mul low first3)
    (by intro we13; exact map_mul_qm_update weights1 we13 q16)

private theorem map_write0_first3_tail (old : CA) (we12 low first3 : C) (q16 : CQ) :
    AspisR1S9CandidateFoldMapPrimitivesV1.mapResult
      (AspisR1S9CandidateFoldMapPrimitivesV1.mapArray
        AspisR1S9CandidateHelperV1.toP6W)
      (do
        let weights1 ← Array.update old 0#usize we12
        let we13 ← AspisR1S9CandidateHelperV1.field.WideExact.mul low first3
        let we14 ← AspisR1S9CandidateHelperV1.field.WideExact.mul_qm31 we13 q16
        Array.update weights1 1#usize we14) =
    (do
      let weights1 ← Array.update
        (AspisR1S9CandidateFoldMapPrimitivesV1.mapArray
          AspisR1S9CandidateHelperV1.toP6W old) 0#usize
        (AspisR1S9CandidateHelperV1.toP6W we12)
      let we13 ← @AspisR1S9HelperP6.FieldOps.wideMul
        AspisR1S9ConcreteFieldOpsV1.concreteFieldOps
        (AspisR1S9CandidateHelperV1.toP6W low)
        (AspisR1S9CandidateHelperV1.toP6W first3)
      let we14 ← @AspisR1S9HelperP6.FieldOps.wideMulQM31
        AspisR1S9ConcreteFieldOpsV1.concreteFieldOps
        we13 (AspisR1S9CandidateHelperV1.toP6Q q16)
      Array.update weights1 1#usize we14) := by
  apply AspisR1S9CandidateFoldMapPrimitivesV1.mapResult_bind_congr
    (AspisR1S9CandidateFoldMapPrimitivesV1.mapArray
      AspisR1S9CandidateHelperV1.toP6W)
    (AspisR1S9CandidateFoldMapPrimitivesV1.mapArray
      AspisR1S9CandidateHelperV1.toP6W)
    (Array.update old 0#usize we12)
    (Array.update
      (AspisR1S9CandidateFoldMapPrimitivesV1.mapArray
        AspisR1S9CandidateHelperV1.toP6W old) 0#usize
      (AspisR1S9CandidateHelperV1.toP6W we12))
    (fun weights1 => do
      let we13 ← AspisR1S9CandidateHelperV1.field.WideExact.mul low first3
      let we14 ← AspisR1S9CandidateHelperV1.field.WideExact.mul_qm31 we13 q16
      Array.update weights1 1#usize we14)
    (fun weights1 => do
      let we13 ← @AspisR1S9HelperP6.FieldOps.wideMul
        AspisR1S9ConcreteFieldOpsV1.concreteFieldOps
        (AspisR1S9CandidateHelperV1.toP6W low)
        (AspisR1S9CandidateHelperV1.toP6W first3)
      let we14 ← @AspisR1S9HelperP6.FieldOps.wideMulQM31
        AspisR1S9ConcreteFieldOpsV1.concreteFieldOps
        we13 (AspisR1S9CandidateHelperV1.toP6Q q16)
      Array.update weights1 1#usize we14)
    (map_update_fixed AspisR1S9CandidateHelperV1.toP6W old 0#usize we12 (by decide))
    (by intro weights1; exact map_mul_first3_tail weights1 low first3 q16)

/-- Full side-zero suffix after term summation, mapped as a Result. -/
theorem candidate_side_zero_tail_maps
    (old : CA) (low first3 all : C) (q16 : CQ) :
    AspisR1S9CandidateFoldMapPrimitivesV1.mapResult
      (AspisR1S9CandidateFoldMapPrimitivesV1.mapArray
        AspisR1S9CandidateHelperV1.toP6W)
      (candidateSideZeroTail old low first3 all q16) =
    AspisR1.S9SideZeroTailRootV1.sideZeroTail
      (AspisR1S9CandidateFoldMapPrimitivesV1.mapArray
        AspisR1S9CandidateHelperV1.toP6W old)
      (AspisR1S9CandidateHelperV1.toP6W low)
      (AspisR1S9CandidateHelperV1.toP6W first3)
      (AspisR1S9CandidateHelperV1.toP6W all)
      (AspisR1S9CandidateHelperV1.toP6Q q16) := by
  unfold candidateSideZeroTail AspisR1.S9SideZeroTailRootV1.sideZeroTail
  apply AspisR1S9CandidateFoldMapPrimitivesV1.mapResult_bind_congr
    (AspisR1S9CandidateFoldMapPrimitivesV1.mapArray
      AspisR1S9CandidateHelperV1.toP6W)
    AspisR1S9CandidateHelperV1.toP6W
    (AspisR1S9CandidateHelperV1.field.WideExact.mul low all)
    (@AspisR1S9HelperP6.FieldOps.wideMul
      AspisR1S9ConcreteFieldOpsV1.concreteFieldOps
      (AspisR1S9CandidateHelperV1.toP6W low)
      (AspisR1S9CandidateHelperV1.toP6W all))
    (fun we12 => do
      let weights1 ← Array.update old 0#usize we12
      let we13 ← AspisR1S9CandidateHelperV1.field.WideExact.mul low first3
      let we14 ← AspisR1S9CandidateHelperV1.field.WideExact.mul_qm31 we13 q16
      Array.update weights1 1#usize we14)
    (fun we12 => do
      let weights1 ← Array.update
        (AspisR1S9CandidateFoldMapPrimitivesV1.mapArray
          AspisR1S9CandidateHelperV1.toP6W old) 0#usize we12
      let we13 ← @AspisR1S9HelperP6.FieldOps.wideMul
        AspisR1S9ConcreteFieldOpsV1.concreteFieldOps
        (AspisR1S9CandidateHelperV1.toP6W low)
        (AspisR1S9CandidateHelperV1.toP6W first3)
      let we14 ← @AspisR1S9HelperP6.FieldOps.wideMulQM31
        AspisR1S9ConcreteFieldOpsV1.concreteFieldOps
        we13 (AspisR1S9CandidateHelperV1.toP6Q q16)
      Array.update weights1 1#usize we14)
    (AspisR1S9CandidateHelperBridgeV1.map_wide_mul low all)
    (by intro we12; exact map_write0_first3_tail old we12 low first3 q16)

#print axioms map_mul_qm_update
#print axioms map_mul_first3_tail
#print axioms map_write0_first3_tail
#print axioms candidate_side_zero_tail_maps

end AspisR1S9CandidateSideZeroTailMapV1
