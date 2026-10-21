import S4OuterFoldTraceV2
import S4FromFnP6OutputResidueAlignedV1
import S4FromFnP6InnerN8ActualResidueV1
import S4FromFnP6OuterSameClosureLoop0V1
import S4FromFnP6InnerN8ConcreteV2

open Aeneas Aeneas.Std Result AspisR1FastDotsCurrent AspisR1FromFnP6Generated
set_option autoImplicit false
namespace AspisR1FastDotsOuterN8BatchResidueV2

abbrev Ops := AspisR1FastDotsCurrent.FourDotsOps
abbrev U8 := Std.U8
abbrev U64 := UScalar UScalarTy.U64
abbrev U32 := Std.U32
abbrev Wide := AspisR1FastDotsCurrent.aspis_core.field.wide_exact.WideExact
abbrev Contribution := AspisR1FastDotsOuterFoldTraceV2.Contribution
abbrev ActualOps (ops : Ops) := AspisR1FastDotsActualSevenBatchLimbBoundV2.ActualBatchOps ops
abbrev Outer (ops : Ops) := AspisR1FastDotsOuterFoldTraceV2.Outer
  (AspisR1FastDotsOuterFoldTraceV2.BatchOps
    (AspisR1FastDotsOuterFoldTraceV2.LimbOps ops))

def indexCell (a : Array U64 8#usize) (i : Fin 8) : Nat :=
  (a.val[i.val]'(by simpa [a.property] using i.isLt)).val

private theorem index_success_bound {α : Type} {n : Usize}
    (a : Array α n) (i : Usize) (x : α)
    (h : Array.index_usize a i = .ok x) : i.val < n.val := by
  have hlen : i.val < a.val.length := by
    by_contra hnot
    have hnone : a[i]? = none := List.getElem?_eq_none (Nat.not_lt.mp hnot)
    unfold Array.index_usize at h
    rw [hnone] at h
    cases h
  simpa [a.property] using hlen

private theorem index_success_eq {α : Type} {n : Usize}
    (a : Array α n) (i : Usize) (x : α)
    (h : Array.index_usize a i = .ok x) :
    x = a.val[i.val]'(by
      have hi := index_success_bound a i x h
      simpa [a.property] using hi) := by
  have hi := index_success_bound a i x h
  have hidx : i.val < a.length := by simpa [a.property] using hi
  obtain ⟨y, hspec, hy⟩ := WP.spec_imp_exists (Array.index_usize_spec a i hidx)
  have hxy : x = y := Result.ok.inj (h.symm.trans hspec)
  exact hxy.trans hy

private theorem reducer_success_actual
    (ops : Ops) (w : U64) (z : AspisR1FastDotsCurrent.aspis_core.field.M31)
    (hbinding : ∀ x, ops.m31ReduceU64 x =
      AspisR1Qm31ArithmeticProbe.field.M31.reduce_u64 x)
    (h : ops.m31ReduceU64 w = .ok z) :
    z.val = w.val % AspisV8R17.RawReducer.P ∧
      z.val < AspisV8R17.RawReducer.P := by
  have hcurrent :
      (AspisR1FastDotsCurrentM31OpsBinding.withCurrentM31ParserReducer ops).m31ReduceU64 w = .ok z := by
    rw [AspisR1FastDotsCurrentM31OpsBinding.reducer_binding, ← hbinding w]
    exact h
  exact AspisR1FastDotsCurrentM31OpsBinding.reducer_success_mod ops w z hcurrent

private theorem actual_n8_array_success_residues
    (ops : Ops) (limbs : Array U64 8#usize) (values : Array U32 8#usize)
    (harray : (AspisR1FromFnP6Generated.fourDotsOpsWithP6ArrayFromFnN4N8
      (AspisR1FastDotsActualSevenBatchLimbBoundV2.ActualBatchOps ops)).arrayFromFn 8#usize
      (fast_dots.four_dots.closure.closure.Insts.CoreOpsFunctionFnMutTupleUsizeU32
        (AspisR1FromFnP6Generated.fourDotsOpsWithP6ArrayFromFnN4N8
          (AspisR1FastDotsActualSevenBatchLimbBoundV2.ActualBatchOps ops))) limbs = .ok values) :
    ∃ w0 w1 w2 w3 w4 w5 w6 w7 : U64,
      Array.index_usize limbs 0#usize = .ok w0 ∧
      Array.index_usize limbs 1#usize = .ok w1 ∧
      Array.index_usize limbs 2#usize = .ok w2 ∧
      Array.index_usize limbs 3#usize = .ok w3 ∧
      Array.index_usize limbs 4#usize = .ok w4 ∧
      Array.index_usize limbs 5#usize = .ok w5 ∧
      Array.index_usize limbs 6#usize = .ok w6 ∧
      Array.index_usize limbs 7#usize = .ok w7 ∧
      values.val.map (fun word => word.val) =
        [w0.val % AspisV8R17.RawReducer.P, w1.val % AspisV8R17.RawReducer.P,
         w2.val % AspisV8R17.RawReducer.P, w3.val % AspisV8R17.RawReducer.P,
         w4.val % AspisV8R17.RawReducer.P, w5.val % AspisV8R17.RawReducer.P,
         w6.val % AspisV8R17.RawReducer.P, w7.val % AspisV8R17.RawReducer.P] ∧
      (∀ value ∈ values.val, value.val < AspisV8R17.RawReducer.P) := by
  let actualOps := AspisR1FastDotsActualSevenBatchLimbBoundV2.ActualBatchOps ops
  let callbackOuter :=
    fast_dots.four_dots.closure.closure.Insts.CoreOpsFunctionFnMutTupleUsizeU32
      (AspisR1FromFnP6Generated.fourDotsOpsWithP6ArrayFromFnN4N8 actualOps)
  let callbackInner :=
    fast_dots.four_dots.closure.closure.Insts.CoreOpsFunctionFnMutTupleUsizeU32
      (AspisR1FromFnP6Generated.fourDotsOpsWithP6ArrayFromFnN8 actualOps)
  have hcallback : callbackOuter = callbackInner := rfl
  have hcallbackArray : arrayFromFnP6 8#usize callbackOuter limbs =
      arrayFromFnP6 8#usize callbackInner limbs :=
    congrArg (fun cb => arrayFromFnP6 8#usize cb limbs) hcallback
  have houter : arrayFromFnP6 8#usize callbackOuter limbs = .ok values := by
    change (if (8#usize).val = 4 then arrayFromFnP6 8#usize callbackOuter limbs
      else if (8#usize).val = 8 then arrayFromFnP6 8#usize callbackOuter limbs
      else actualOps.arrayFromFn 8#usize callbackOuter limbs) = .ok values at harray
    simpa only [if_neg (by decide : (8#usize).val ≠ 4),
      if_pos (by decide : (8#usize).val = 8)] using harray
  have hinnerP6 : arrayFromFnP6 8#usize callbackInner limbs = .ok values :=
    hcallbackArray.symm.trans houter
  have hmodel : (AspisR1FromFnP6Generated.fourDotsOpsWithP6ArrayFromFnN8 actualOps).arrayFromFn
      8#usize callbackInner limbs = .ok values := by
    simpa only [AspisR1FromFnP6Generated.fourDotsOpsWithP6ArrayFromFnN8,
      if_pos (by decide : (8#usize).val = 8)] using hinnerP6
  obtain ⟨m0,m1,m2,m3,m4,m5,m6,m7,w0,w1,w2,w3,w4,w5,w6,w7,
      hvalues,hi0,hr0,hi1,hr1,hi2,hr2,hi3,hr3,hi4,hr4,hi5,hr5,hi6,hr6,hi7,hr7⟩ :=
    AspisR1FromFnP6Generated.generatedInnerN8ArrayField_success_values_match_fixedV6
      actualOps limbs values hmodel
  have hbinding : ∀ x, actualOps.m31ReduceU64 x =
      AspisR1Qm31ArithmeticProbe.field.M31.reduce_u64 x := by
    intro x
    rfl
  have ⟨hm0,hc0⟩ := reducer_success_actual actualOps w0 m0 hbinding hr0
  have ⟨hm1,hc1⟩ := reducer_success_actual actualOps w1 m1 hbinding hr1
  have ⟨hm2,hc2⟩ := reducer_success_actual actualOps w2 m2 hbinding hr2
  have ⟨hm3,hc3⟩ := reducer_success_actual actualOps w3 m3 hbinding hr3
  have ⟨hm4,hc4⟩ := reducer_success_actual actualOps w4 m4 hbinding hr4
  have ⟨hm5,hc5⟩ := reducer_success_actual actualOps w5 m5 hbinding hr5
  have ⟨hm6,hc6⟩ := reducer_success_actual actualOps w6 m6 hbinding hr6
  have ⟨hm7,hc7⟩ := reducer_success_actual actualOps w7 m7 hbinding hr7
  refine ⟨w0,w1,w2,w3,w4,w5,w6,w7,hi0,hi1,hi2,hi3,hi4,hi5,hi6,hi7,?_,?_⟩
  · simp only [hvalues,List.map_cons,List.map_nil,hm0,hm1,hm2,hm3,hm4,hm5,hm6,hm7]
  · intro value hv
    rw [hvalues] at hv
    simp only [List.mem_cons,List.not_mem_nil,or_false] at hv
    rcases hv with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption

/-- A generic slot-local adapter: one actual outer call and the matching N8
    array call yield the residue vector of that slot's exact parsed batches. -/
theorem actual_n8_batch_residue_from_calls
    (ops : Ops) (a : Array U8 608#usize) (g : Array Wide 29#usize)
    (slot : Usize)
    (hcoords : ∀ i : Fin 29,
      AspisR1FastDotsWideLimbCanonical.CoordinateBound
        (g.val[i.val]'(by simpa [g.property] using i.isLt)))
    (limbs : Array U64 8#usize) (values : Array U32 8#usize)
    (houter : Outer ops AspisR1FastDotsStepSchedule.startBy a g slot
      (Array.repeat 8#usize 0#u64) = .ok limbs)
    (harray : (AspisR1FromFnP6Generated.fourDotsOpsWithP6ArrayFromFnN4N8
      (AspisR1FastDotsActualSevenBatchLimbBoundV2.ActualBatchOps ops)).arrayFromFn 8#usize
      (fast_dots.four_dots.closure.closure.Insts.CoreOpsFunctionFnMutTupleUsizeU32
        (AspisR1FromFnP6Generated.fourDotsOpsWithP6ArrayFromFnN4N8
          (AspisR1FastDotsActualSevenBatchLimbBoundV2.ActualBatchOps ops))) limbs = .ok values) :
    ∃ ds starts,
      AspisR1FastDotsOuterFoldTraceV2.ExactTrace ops a g slot
        AspisR1FastDotsStepSchedule.startBy (Array.repeat 8#usize 0#u64) limbs ds starts ∧
      ds.length = 7 ∧
      values.val.map (fun word => word.val) =
        [AspisR1.FastDotFoldedBatches.fullSum
            (AspisR1FastDotsOuterFoldTraceV2.rawBatchLists ds ⟨0,by decide⟩) % AspisR1BatchedFoldArithmetic.modulus,
         AspisR1.FastDotFoldedBatches.fullSum
            (AspisR1FastDotsOuterFoldTraceV2.rawBatchLists ds ⟨1,by decide⟩) % AspisR1BatchedFoldArithmetic.modulus,
         AspisR1.FastDotFoldedBatches.fullSum
            (AspisR1FastDotsOuterFoldTraceV2.rawBatchLists ds ⟨2,by decide⟩) % AspisR1BatchedFoldArithmetic.modulus,
         AspisR1.FastDotFoldedBatches.fullSum
            (AspisR1FastDotsOuterFoldTraceV2.rawBatchLists ds ⟨3,by decide⟩) % AspisR1BatchedFoldArithmetic.modulus,
         AspisR1.FastDotFoldedBatches.fullSum
            (AspisR1FastDotsOuterFoldTraceV2.rawBatchLists ds ⟨4,by decide⟩) % AspisR1BatchedFoldArithmetic.modulus,
         AspisR1.FastDotFoldedBatches.fullSum
            (AspisR1FastDotsOuterFoldTraceV2.rawBatchLists ds ⟨5,by decide⟩) % AspisR1BatchedFoldArithmetic.modulus,
         AspisR1.FastDotFoldedBatches.fullSum
            (AspisR1FastDotsOuterFoldTraceV2.rawBatchLists ds ⟨6,by decide⟩) % AspisR1BatchedFoldArithmetic.modulus,
         AspisR1.FastDotFoldedBatches.fullSum
            (AspisR1FastDotsOuterFoldTraceV2.rawBatchLists ds ⟨7,by decide⟩) % AspisR1BatchedFoldArithmetic.modulus] ∧
      (∀ value ∈ values.val, value.val < AspisV8R17.RawReducer.P) := by
  obtain ⟨ds,starts,htrace,hseven,hlimits,hres⟩ :=
    AspisR1FastDotsOuterFoldTraceV2.actual_outer_success_reducer_residue
      ops a g slot limbs hcoords houter
  obtain ⟨w0,w1,w2,w3,w4,w5,w6,w7,hi0,hi1,hi2,hi3,hi4,hi5,hi6,hi7,
      hresidues,hcanonical⟩ := actual_n8_array_success_residues ops limbs values harray
  have hidx0 := index_success_eq limbs 0#usize w0 hi0
  have hidx1 := index_success_eq limbs 1#usize w1 hi1
  have hidx2 := index_success_eq limbs 2#usize w2 hi2
  have hidx3 := index_success_eq limbs 3#usize w3 hi3
  have hidx4 := index_success_eq limbs 4#usize w4 hi4
  have hidx5 := index_success_eq limbs 5#usize w5 hi5
  have hidx6 := index_success_eq limbs 6#usize w6 hi6
  have hidx7 := index_success_eq limbs 7#usize w7 hi7
  have hword0 : w0.val % AspisV8R17.RawReducer.P =
      AspisR1.FastDotFoldedBatches.fullSum
        (AspisR1FastDotsOuterFoldTraceV2.rawBatchLists ds ⟨0,by decide⟩) %
        AspisR1BatchedFoldArithmetic.modulus := by
    obtain ⟨z,hred,hz,_⟩ := hres ⟨0,by decide⟩
    have hredCell := hred
    change AspisR1Qm31ArithmeticProbe.field.M31.reduce_u64 (limbs.val[0]) = .ok z at hredCell
    have hidxCell := hidx0
    change w0 = limbs.val[0] at hidxCell
    rw [← hidxCell] at hredCell
    have hcurrent :
        (AspisR1FastDotsCurrentM31OpsBinding.withCurrentM31ParserReducer
          (AspisR1FastDotsOuterFoldTraceV2.ActualOps ops)).m31ReduceU64 w0 = .ok z := by
      rw [AspisR1FastDotsCurrentM31OpsBinding.reducer_binding]
      exact hredCell
    have hmod := AspisR1FastDotsCurrentM31OpsBinding.reducer_success_mod
      (AspisR1FastDotsOuterFoldTraceV2.ActualOps ops) w0 z hcurrent
    rw [AspisR1BatchedFoldArithmetic.modulus]
    exact hmod.1.symm.trans hz
  have hword1 : w1.val % AspisV8R17.RawReducer.P =
      AspisR1.FastDotFoldedBatches.fullSum
        (AspisR1FastDotsOuterFoldTraceV2.rawBatchLists ds ⟨1,by decide⟩) %
        AspisR1BatchedFoldArithmetic.modulus := by
    obtain ⟨z,hred,hz,_⟩ := hres ⟨1,by decide⟩
    have hredCell := hred
    change AspisR1Qm31ArithmeticProbe.field.M31.reduce_u64 (limbs.val[1]) = .ok z at hredCell
    have hidxCell := hidx1
    change w1 = limbs.val[1] at hidxCell
    rw [← hidxCell] at hredCell
    have hcurrent :
        (AspisR1FastDotsCurrentM31OpsBinding.withCurrentM31ParserReducer
          (AspisR1FastDotsOuterFoldTraceV2.ActualOps ops)).m31ReduceU64 w1 = .ok z := by
      rw [AspisR1FastDotsCurrentM31OpsBinding.reducer_binding]
      exact hredCell
    have hmod := AspisR1FastDotsCurrentM31OpsBinding.reducer_success_mod
      (AspisR1FastDotsOuterFoldTraceV2.ActualOps ops) w1 z hcurrent
    rw [AspisR1BatchedFoldArithmetic.modulus]
    exact hmod.1.symm.trans hz
  have hword2 : w2.val % AspisV8R17.RawReducer.P =
      AspisR1.FastDotFoldedBatches.fullSum
        (AspisR1FastDotsOuterFoldTraceV2.rawBatchLists ds ⟨2,by decide⟩) %
        AspisR1BatchedFoldArithmetic.modulus := by
    obtain ⟨z,hred,hz,_⟩ := hres ⟨2,by decide⟩
    have hredCell := hred
    change AspisR1Qm31ArithmeticProbe.field.M31.reduce_u64 (limbs.val[2]) = .ok z at hredCell
    have hidxCell := hidx2
    change w2 = limbs.val[2] at hidxCell
    rw [← hidxCell] at hredCell
    have hcurrent :
        (AspisR1FastDotsCurrentM31OpsBinding.withCurrentM31ParserReducer
          (AspisR1FastDotsOuterFoldTraceV2.ActualOps ops)).m31ReduceU64 w2 = .ok z := by
      rw [AspisR1FastDotsCurrentM31OpsBinding.reducer_binding]
      exact hredCell
    have hmod := AspisR1FastDotsCurrentM31OpsBinding.reducer_success_mod
      (AspisR1FastDotsOuterFoldTraceV2.ActualOps ops) w2 z hcurrent
    rw [AspisR1BatchedFoldArithmetic.modulus]
    exact hmod.1.symm.trans hz
  have hword3 : w3.val % AspisV8R17.RawReducer.P =
      AspisR1.FastDotFoldedBatches.fullSum
        (AspisR1FastDotsOuterFoldTraceV2.rawBatchLists ds ⟨3,by decide⟩) %
        AspisR1BatchedFoldArithmetic.modulus := by
    obtain ⟨z,hred,hz,_⟩ := hres ⟨3,by decide⟩
    have hredCell := hred
    change AspisR1Qm31ArithmeticProbe.field.M31.reduce_u64 (limbs.val[3]) = .ok z at hredCell
    have hidxCell := hidx3
    change w3 = limbs.val[3] at hidxCell
    rw [← hidxCell] at hredCell
    have hcurrent :
        (AspisR1FastDotsCurrentM31OpsBinding.withCurrentM31ParserReducer
          (AspisR1FastDotsOuterFoldTraceV2.ActualOps ops)).m31ReduceU64 w3 = .ok z := by
      rw [AspisR1FastDotsCurrentM31OpsBinding.reducer_binding]
      exact hredCell
    have hmod := AspisR1FastDotsCurrentM31OpsBinding.reducer_success_mod
      (AspisR1FastDotsOuterFoldTraceV2.ActualOps ops) w3 z hcurrent
    rw [AspisR1BatchedFoldArithmetic.modulus]
    exact hmod.1.symm.trans hz
  have hword4 : w4.val % AspisV8R17.RawReducer.P =
      AspisR1.FastDotFoldedBatches.fullSum
        (AspisR1FastDotsOuterFoldTraceV2.rawBatchLists ds ⟨4,by decide⟩) %
        AspisR1BatchedFoldArithmetic.modulus := by
    obtain ⟨z,hred,hz,_⟩ := hres ⟨4,by decide⟩
    have hredCell := hred
    change AspisR1Qm31ArithmeticProbe.field.M31.reduce_u64 (limbs.val[4]) = .ok z at hredCell
    have hidxCell := hidx4
    change w4 = limbs.val[4] at hidxCell
    rw [← hidxCell] at hredCell
    have hcurrent :
        (AspisR1FastDotsCurrentM31OpsBinding.withCurrentM31ParserReducer
          (AspisR1FastDotsOuterFoldTraceV2.ActualOps ops)).m31ReduceU64 w4 = .ok z := by
      rw [AspisR1FastDotsCurrentM31OpsBinding.reducer_binding]
      exact hredCell
    have hmod := AspisR1FastDotsCurrentM31OpsBinding.reducer_success_mod
      (AspisR1FastDotsOuterFoldTraceV2.ActualOps ops) w4 z hcurrent
    rw [AspisR1BatchedFoldArithmetic.modulus]
    exact hmod.1.symm.trans hz
  have hword5 : w5.val % AspisV8R17.RawReducer.P =
      AspisR1.FastDotFoldedBatches.fullSum
        (AspisR1FastDotsOuterFoldTraceV2.rawBatchLists ds ⟨5,by decide⟩) %
        AspisR1BatchedFoldArithmetic.modulus := by
    obtain ⟨z,hred,hz,_⟩ := hres ⟨5,by decide⟩
    have hredCell := hred
    change AspisR1Qm31ArithmeticProbe.field.M31.reduce_u64 (limbs.val[5]) = .ok z at hredCell
    have hidxCell := hidx5
    change w5 = limbs.val[5] at hidxCell
    rw [← hidxCell] at hredCell
    have hcurrent :
        (AspisR1FastDotsCurrentM31OpsBinding.withCurrentM31ParserReducer
          (AspisR1FastDotsOuterFoldTraceV2.ActualOps ops)).m31ReduceU64 w5 = .ok z := by
      rw [AspisR1FastDotsCurrentM31OpsBinding.reducer_binding]
      exact hredCell
    have hmod := AspisR1FastDotsCurrentM31OpsBinding.reducer_success_mod
      (AspisR1FastDotsOuterFoldTraceV2.ActualOps ops) w5 z hcurrent
    rw [AspisR1BatchedFoldArithmetic.modulus]
    exact hmod.1.symm.trans hz
  have hword6 : w6.val % AspisV8R17.RawReducer.P =
      AspisR1.FastDotFoldedBatches.fullSum
        (AspisR1FastDotsOuterFoldTraceV2.rawBatchLists ds ⟨6,by decide⟩) %
        AspisR1BatchedFoldArithmetic.modulus := by
    obtain ⟨z,hred,hz,_⟩ := hres ⟨6,by decide⟩
    have hredCell := hred
    change AspisR1Qm31ArithmeticProbe.field.M31.reduce_u64 (limbs.val[6]) = .ok z at hredCell
    have hidxCell := hidx6
    change w6 = limbs.val[6] at hidxCell
    rw [← hidxCell] at hredCell
    have hcurrent :
        (AspisR1FastDotsCurrentM31OpsBinding.withCurrentM31ParserReducer
          (AspisR1FastDotsOuterFoldTraceV2.ActualOps ops)).m31ReduceU64 w6 = .ok z := by
      rw [AspisR1FastDotsCurrentM31OpsBinding.reducer_binding]
      exact hredCell
    have hmod := AspisR1FastDotsCurrentM31OpsBinding.reducer_success_mod
      (AspisR1FastDotsOuterFoldTraceV2.ActualOps ops) w6 z hcurrent
    rw [AspisR1BatchedFoldArithmetic.modulus]
    exact hmod.1.symm.trans hz
  have hword7 : w7.val % AspisV8R17.RawReducer.P =
      AspisR1.FastDotFoldedBatches.fullSum
        (AspisR1FastDotsOuterFoldTraceV2.rawBatchLists ds ⟨7,by decide⟩) %
        AspisR1BatchedFoldArithmetic.modulus := by
    obtain ⟨z,hred,hz,_⟩ := hres ⟨7,by decide⟩
    have hredCell := hred
    change AspisR1Qm31ArithmeticProbe.field.M31.reduce_u64 (limbs.val[7]) = .ok z at hredCell
    have hidxCell := hidx7
    change w7 = limbs.val[7] at hidxCell
    rw [← hidxCell] at hredCell
    have hcurrent :
        (AspisR1FastDotsCurrentM31OpsBinding.withCurrentM31ParserReducer
          (AspisR1FastDotsOuterFoldTraceV2.ActualOps ops)).m31ReduceU64 w7 = .ok z := by
      rw [AspisR1FastDotsCurrentM31OpsBinding.reducer_binding]
      exact hredCell
    have hmod := AspisR1FastDotsCurrentM31OpsBinding.reducer_success_mod
      (AspisR1FastDotsOuterFoldTraceV2.ActualOps ops) w7 z hcurrent
    rw [AspisR1BatchedFoldArithmetic.modulus]
    exact hmod.1.symm.trans hz
  refine ⟨ds,starts,htrace,hseven,?_,hcanonical⟩
  rw [hresidues,hword0,hword1,hword2,hword3,hword4,hword5,hword6,hword7]

def SlotBatchOutput (ops : Ops) (a : Array U8 608#usize) (g : Array Wide 29#usize)
    (slot : Usize) (limbs : Array U64 8#usize) (values : Array U32 8#usize) : Prop :=
  Outer ops AspisR1FastDotsStepSchedule.startBy a g slot
      (Array.repeat 8#usize 0#u64) = .ok limbs ∧
  (AspisR1FromFnP6Generated.fourDotsOpsWithP6ArrayFromFnN4N8
    (AspisR1FastDotsActualSevenBatchLimbBoundV2.ActualBatchOps ops)).arrayFromFn 8#usize
    (fast_dots.four_dots.closure.closure.Insts.CoreOpsFunctionFnMutTupleUsizeU32
      (AspisR1FromFnP6Generated.fourDotsOpsWithP6ArrayFromFnN4N8
        (AspisR1FastDotsActualSevenBatchLimbBoundV2.ActualBatchOps ops))) limbs = .ok values ∧
  ∃ ds starts,
    AspisR1FastDotsOuterFoldTraceV2.ExactTrace ops a g slot
      AspisR1FastDotsStepSchedule.startBy (Array.repeat 8#usize 0#u64) limbs ds starts ∧
    ds.length = 7 ∧
    values.val.map (fun word => word.val) =
      [AspisR1.FastDotFoldedBatches.fullSum
          (AspisR1FastDotsOuterFoldTraceV2.rawBatchLists ds ⟨0,by decide⟩) % AspisR1BatchedFoldArithmetic.modulus,
       AspisR1.FastDotFoldedBatches.fullSum
          (AspisR1FastDotsOuterFoldTraceV2.rawBatchLists ds ⟨1,by decide⟩) % AspisR1BatchedFoldArithmetic.modulus,
       AspisR1.FastDotFoldedBatches.fullSum
          (AspisR1FastDotsOuterFoldTraceV2.rawBatchLists ds ⟨2,by decide⟩) % AspisR1BatchedFoldArithmetic.modulus,
       AspisR1.FastDotFoldedBatches.fullSum
          (AspisR1FastDotsOuterFoldTraceV2.rawBatchLists ds ⟨3,by decide⟩) % AspisR1BatchedFoldArithmetic.modulus,
       AspisR1.FastDotFoldedBatches.fullSum
          (AspisR1FastDotsOuterFoldTraceV2.rawBatchLists ds ⟨4,by decide⟩) % AspisR1BatchedFoldArithmetic.modulus,
       AspisR1.FastDotFoldedBatches.fullSum
          (AspisR1FastDotsOuterFoldTraceV2.rawBatchLists ds ⟨5,by decide⟩) % AspisR1BatchedFoldArithmetic.modulus,
       AspisR1.FastDotFoldedBatches.fullSum
          (AspisR1FastDotsOuterFoldTraceV2.rawBatchLists ds ⟨6,by decide⟩) % AspisR1BatchedFoldArithmetic.modulus,
       AspisR1.FastDotFoldedBatches.fullSum
          (AspisR1FastDotsOuterFoldTraceV2.rawBatchLists ds ⟨7,by decide⟩) % AspisR1BatchedFoldArithmetic.modulus] ∧
    (∀ value ∈ values.val, value.val < AspisV8R17.RawReducer.P)

theorem actual_n8_batch_residue_from_calls_output
    (ops : Ops) (a : Array U8 608#usize) (g : Array Wide 29#usize)
    (slot : Usize)
    (hcoords : ∀ i : Fin 29,
      AspisR1FastDotsWideLimbCanonical.CoordinateBound
        (g.val[i.val]'(by simpa [g.property] using i.isLt)))
    (limbs : Array U64 8#usize) (values : Array U32 8#usize)
    (houter : Outer ops AspisR1FastDotsStepSchedule.startBy a g slot
      (Array.repeat 8#usize 0#u64) = .ok limbs)
    (harray : (AspisR1FromFnP6Generated.fourDotsOpsWithP6ArrayFromFnN4N8
      (AspisR1FastDotsActualSevenBatchLimbBoundV2.ActualBatchOps ops)).arrayFromFn 8#usize
      (fast_dots.four_dots.closure.closure.Insts.CoreOpsFunctionFnMutTupleUsizeU32
        (AspisR1FromFnP6Generated.fourDotsOpsWithP6ArrayFromFnN4N8
          (AspisR1FastDotsActualSevenBatchLimbBoundV2.ActualBatchOps ops))) limbs = .ok values) :
    SlotBatchOutput ops a g slot limbs values := by
  obtain ⟨ds,starts,htrace,hseven,hmap,hcanonical⟩ :=
    actual_n8_batch_residue_from_calls ops a g slot hcoords limbs values houter harray
  exact ⟨houter,harray,⟨ds,starts,htrace,hseven,hmap,hcanonical⟩⟩

/-- All four outputs are tied to the same successful generated N4 array call. -/
theorem generatedFourDotsN4_success_all_n8_batch_residues
    (ops : Ops) (a : Array U8 608#usize) (g : Array Wide 29#usize)
    (hcoords : ∀ i : Fin 29,
      AspisR1FastDotsWideLimbCanonical.CoordinateBound
        (g.val[i.val]'(by simpa [g.property] using i.isLt)))
    {values : Array Wide 4#usize}
    (h : (AspisR1FromFnP6Generated.fourDotsOpsWithP6ArrayFromFnN4N8
      (AspisR1FastDotsActualSevenBatchLimbBoundV2.ActualBatchOps ops)).arrayFromFn 4#usize
      (fast_dots.four_dots.closure.Insts.CoreOpsFunctionFnMutTupleUsizeWideExact
        (AspisR1FromFnP6Generated.fourDotsOpsWithP6ArrayFromFnN4N8
          (AspisR1FastDotsActualSevenBatchLimbBoundV2.ActualBatchOps ops))) (a,g) = .ok values) :
    ∃ (v0 v1 v2 v3 : Wide)
      (limbs0 limbs1 limbs2 limbs3 : Array U64 8#usize)
      (vals0 vals1 vals2 vals3 : Array U32 8#usize),
      values.val = [v0,v1,v2,v3] ∧
      SlotBatchOutput ops a g 0#usize limbs0 vals0 ∧
      SlotBatchOutput ops a g 1#usize limbs1 vals1 ∧
      SlotBatchOutput ops a g 2#usize limbs2 vals2 ∧
      SlotBatchOutput ops a g 3#usize limbs3 vals3 := by
  obtain ⟨v0,v1,v2,v3,limbs0,limbs1,limbs2,limbs3,vals0,vals1,vals2,vals3,
      hvalues,hcall0,hcall1,hcall2,hcall3,hstep,
      hloop0,harray0,hloop1,harray1,hloop2,harray2,hloop3,harray3⟩ :=
    AspisR1FromFnP6Generated.generatedFourDotsN4_success_same_closure_loop0_four_calls
      (AspisR1FastDotsActualSevenBatchLimbBoundV2.ActualBatchOps ops) a g h
  have hstartEq := Result.ok.inj
    (hstep.symm.trans AspisR1FastDotsStepSchedule.initialized_step_by)
  have hloopStart0 : fast_dots.four_dots.closure.Insts.CoreOpsFunctionFnMutTupleUsizeWideExact.call_mut_loop0
      (AspisR1FromFnP6Generated.fourDotsOpsWithP6ArrayFromFnN4N8
        (AspisR1FastDotsActualSevenBatchLimbBoundV2.ActualBatchOps ops))
      AspisR1FastDotsStepSchedule.startBy a g 0#usize
      (Array.repeat 8#usize 0#u64) = .ok limbs0 := by simpa only [hstartEq] using hloop0
  have hloopStart1 : fast_dots.four_dots.closure.Insts.CoreOpsFunctionFnMutTupleUsizeWideExact.call_mut_loop0
      (AspisR1FromFnP6Generated.fourDotsOpsWithP6ArrayFromFnN4N8
        (AspisR1FastDotsActualSevenBatchLimbBoundV2.ActualBatchOps ops))
      AspisR1FastDotsStepSchedule.startBy a g 1#usize
      (Array.repeat 8#usize 0#u64) = .ok limbs1 := by simpa only [hstartEq] using hloop1
  have hloopStart2 : fast_dots.four_dots.closure.Insts.CoreOpsFunctionFnMutTupleUsizeWideExact.call_mut_loop0
      (AspisR1FromFnP6Generated.fourDotsOpsWithP6ArrayFromFnN4N8
        (AspisR1FastDotsActualSevenBatchLimbBoundV2.ActualBatchOps ops))
      AspisR1FastDotsStepSchedule.startBy a g 2#usize
      (Array.repeat 8#usize 0#u64) = .ok limbs2 := by simpa only [hstartEq] using hloop2
  have hloopStart3 : fast_dots.four_dots.closure.Insts.CoreOpsFunctionFnMutTupleUsizeWideExact.call_mut_loop0
      (AspisR1FromFnP6Generated.fourDotsOpsWithP6ArrayFromFnN4N8
        (AspisR1FastDotsActualSevenBatchLimbBoundV2.ActualBatchOps ops))
      AspisR1FastDotsStepSchedule.startBy a g 3#usize
      (Array.repeat 8#usize 0#u64) = .ok limbs3 := by simpa only [hstartEq] using hloop3
  have hloopActual0 := hloopStart0
  have hloopActual1 := hloopStart1
  have hloopActual2 := hloopStart2
  have hloopActual3 := hloopStart3
  rw [AspisR1FromFnP6Generated.generatedLoop0_ignores_p6_array_adapter
    (AspisR1FastDotsActualSevenBatchLimbBoundV2.ActualBatchOps ops) _ a g 0#usize _] at hloopActual0
  rw [AspisR1FromFnP6Generated.generatedLoop0_ignores_p6_array_adapter
    (AspisR1FastDotsActualSevenBatchLimbBoundV2.ActualBatchOps ops) _ a g 1#usize _] at hloopActual1
  rw [AspisR1FromFnP6Generated.generatedLoop0_ignores_p6_array_adapter
    (AspisR1FastDotsActualSevenBatchLimbBoundV2.ActualBatchOps ops) _ a g 2#usize _] at hloopActual2
  rw [AspisR1FromFnP6Generated.generatedLoop0_ignores_p6_array_adapter
    (AspisR1FastDotsActualSevenBatchLimbBoundV2.ActualBatchOps ops) _ a g 3#usize _] at hloopActual3
  have houter0 : Outer ops AspisR1FastDotsStepSchedule.startBy a g 0#usize
      (Array.repeat 8#usize 0#u64) = .ok limbs0 := by
    change AspisR1FastDotsOuterFoldTraceV2.Outer
      (AspisR1FastDotsOuterFoldTraceV2.BatchOps
        (AspisR1FastDotsOuterFoldTraceV2.LimbOps ops))
      AspisR1FastDotsStepSchedule.startBy a g 0#usize
      (Array.repeat 8#usize 0#u64) = .ok limbs0
    exact hloopActual0
  have houter1 : Outer ops AspisR1FastDotsStepSchedule.startBy a g 1#usize
      (Array.repeat 8#usize 0#u64) = .ok limbs1 := by
    change AspisR1FastDotsOuterFoldTraceV2.Outer
      (AspisR1FastDotsOuterFoldTraceV2.BatchOps
        (AspisR1FastDotsOuterFoldTraceV2.LimbOps ops))
      AspisR1FastDotsStepSchedule.startBy a g 1#usize
      (Array.repeat 8#usize 0#u64) = .ok limbs1
    exact hloopActual1
  have houter2 : Outer ops AspisR1FastDotsStepSchedule.startBy a g 2#usize
      (Array.repeat 8#usize 0#u64) = .ok limbs2 := by
    change AspisR1FastDotsOuterFoldTraceV2.Outer
      (AspisR1FastDotsOuterFoldTraceV2.BatchOps
        (AspisR1FastDotsOuterFoldTraceV2.LimbOps ops))
      AspisR1FastDotsStepSchedule.startBy a g 2#usize
      (Array.repeat 8#usize 0#u64) = .ok limbs2
    exact hloopActual2
  have houter3 : Outer ops AspisR1FastDotsStepSchedule.startBy a g 3#usize
      (Array.repeat 8#usize 0#u64) = .ok limbs3 := by
    change AspisR1FastDotsOuterFoldTraceV2.Outer
      (AspisR1FastDotsOuterFoldTraceV2.BatchOps
        (AspisR1FastDotsOuterFoldTraceV2.LimbOps ops))
      AspisR1FastDotsStepSchedule.startBy a g 3#usize
      (Array.repeat 8#usize 0#u64) = .ok limbs3
    exact hloopActual3
  have hslot0 := actual_n8_batch_residue_from_calls_output
    ops a g 0#usize hcoords limbs0 vals0 houter0 harray0
  have hslot1 := actual_n8_batch_residue_from_calls_output
    ops a g 1#usize hcoords limbs1 vals1 houter1 harray1
  have hslot2 := actual_n8_batch_residue_from_calls_output
    ops a g 2#usize hcoords limbs2 vals2 houter2 harray2
  have hslot3 := actual_n8_batch_residue_from_calls_output
    ops a g 3#usize hcoords limbs3 vals3 houter3 harray3
  exact ⟨v0,v1,v2,v3,limbs0,limbs1,limbs2,limbs3,vals0,vals1,vals2,vals3,
    hvalues,hslot0,hslot1,hslot2,hslot3⟩

#print axioms generatedFourDotsN4_success_all_n8_batch_residues


/-- One successful original four-result constructor exposes this same slot's
    actual loop0 and N8 callback. The N8 array's words are the residues of the
    exact parsed products retained in that loop's seven-batch trace. -/
theorem generatedFourDotsSlot0_success_actual_n8_batch_residue
    (ops : Ops) (a : Array U8 608#usize) (g : Array Wide 29#usize)
    (hcoords : ∀ i : Fin 29,
      AspisR1FastDotsWideLimbCanonical.CoordinateBound
        (g.val[i.val]'(by simpa [g.property] using i.isLt)))
    {values : Array Wide 4#usize}
    (h : (AspisR1FromFnP6Generated.fourDotsOpsWithP6ArrayFromFnN4N8
      (AspisR1FastDotsActualSevenBatchLimbBoundV2.ActualBatchOps ops)).arrayFromFn 4#usize
      (fast_dots.four_dots.closure.Insts.CoreOpsFunctionFnMutTupleUsizeWideExact
        (AspisR1FromFnP6Generated.fourDotsOpsWithP6ArrayFromFnN4N8
          (AspisR1FastDotsActualSevenBatchLimbBoundV2.ActualBatchOps ops))) (a,g) = .ok values) :
    ∃ (v0 v1 v2 v3 : Wide) (limbs0 limbs1 limbs2 limbs3 : Array U64 8#usize)
      (vals0 vals1 vals2 vals3 : Array U32 8#usize) (ds : List (List Contribution))
      (starts : List Nat),
      values.val = [v0,v1,v2,v3] ∧
      fast_dots.four_dots.closure.Insts.CoreOpsFunctionFnMutTupleUsizeWideExact.call_mut_loop0
        (AspisR1FromFnP6Generated.fourDotsOpsWithP6ArrayFromFnN4N8
          (AspisR1FastDotsActualSevenBatchLimbBoundV2.ActualBatchOps ops))
        AspisR1FastDotsStepSchedule.startBy a g 0#usize (Array.repeat 8#usize 0#u64) = .ok limbs0 ∧
      (AspisR1FromFnP6Generated.fourDotsOpsWithP6ArrayFromFnN4N8
        (AspisR1FastDotsActualSevenBatchLimbBoundV2.ActualBatchOps ops)).arrayFromFn 8#usize
        (fast_dots.four_dots.closure.closure.Insts.CoreOpsFunctionFnMutTupleUsizeU32
          (AspisR1FromFnP6Generated.fourDotsOpsWithP6ArrayFromFnN4N8
            (AspisR1FastDotsActualSevenBatchLimbBoundV2.ActualBatchOps ops))) limbs0 = .ok vals0 ∧
      AspisR1FastDotsOuterFoldTraceV2.ExactTrace ops a g 0#usize
        AspisR1FastDotsStepSchedule.startBy (Array.repeat 8#usize 0#u64) limbs0 ds starts ∧
      ds.length = 7 ∧
      vals0.val.map (fun word => word.val) =
        [AspisR1.FastDotFoldedBatches.fullSum
            (AspisR1FastDotsOuterFoldTraceV2.rawBatchLists ds ⟨0,by decide⟩) % AspisR1BatchedFoldArithmetic.modulus,
         AspisR1.FastDotFoldedBatches.fullSum
            (AspisR1FastDotsOuterFoldTraceV2.rawBatchLists ds ⟨1,by decide⟩) % AspisR1BatchedFoldArithmetic.modulus,
         AspisR1.FastDotFoldedBatches.fullSum
            (AspisR1FastDotsOuterFoldTraceV2.rawBatchLists ds ⟨2,by decide⟩) % AspisR1BatchedFoldArithmetic.modulus,
         AspisR1.FastDotFoldedBatches.fullSum
            (AspisR1FastDotsOuterFoldTraceV2.rawBatchLists ds ⟨3,by decide⟩) % AspisR1BatchedFoldArithmetic.modulus,
         AspisR1.FastDotFoldedBatches.fullSum
            (AspisR1FastDotsOuterFoldTraceV2.rawBatchLists ds ⟨4,by decide⟩) % AspisR1BatchedFoldArithmetic.modulus,
         AspisR1.FastDotFoldedBatches.fullSum
            (AspisR1FastDotsOuterFoldTraceV2.rawBatchLists ds ⟨5,by decide⟩) % AspisR1BatchedFoldArithmetic.modulus,
         AspisR1.FastDotFoldedBatches.fullSum
            (AspisR1FastDotsOuterFoldTraceV2.rawBatchLists ds ⟨6,by decide⟩) % AspisR1BatchedFoldArithmetic.modulus,
         AspisR1.FastDotFoldedBatches.fullSum
            (AspisR1FastDotsOuterFoldTraceV2.rawBatchLists ds ⟨7,by decide⟩) % AspisR1BatchedFoldArithmetic.modulus] ∧
      (∀ value ∈ vals0.val, value.val < AspisV8R17.RawReducer.P) := by
  obtain ⟨v0,v1,v2,v3,limbs0,limbs1,limbs2,limbs3,vals0,vals1,vals2,vals3,
      hvalues,hcall0,hcall1,hcall2,hcall3,hstep,
      hloop0,harray0,hloop1,harray1,hloop2,harray2,hloop3,harray3⟩ :=
    AspisR1FromFnP6Generated.generatedFourDotsN4_success_same_closure_loop0_four_calls
      (AspisR1FastDotsActualSevenBatchLimbBoundV2.ActualBatchOps ops) a g h
  have hstartEq := Result.ok.inj
    (hstep.symm.trans AspisR1FastDotsStepSchedule.initialized_step_by)
  have hloopStart : fast_dots.four_dots.closure.Insts.CoreOpsFunctionFnMutTupleUsizeWideExact.call_mut_loop0
      (AspisR1FromFnP6Generated.fourDotsOpsWithP6ArrayFromFnN4N8
        (AspisR1FastDotsActualSevenBatchLimbBoundV2.ActualBatchOps ops))
      AspisR1FastDotsStepSchedule.startBy a g 0#usize
      (Array.repeat 8#usize 0#u64) = .ok limbs0 := by
    simpa only [hstartEq] using hloop0
  have hloopActual := hloopStart
  rw [AspisR1FromFnP6Generated.generatedLoop0_ignores_p6_array_adapter
    (AspisR1FastDotsActualSevenBatchLimbBoundV2.ActualBatchOps ops) _ a g 0#usize _] at hloopActual
  have houter : Outer ops AspisR1FastDotsStepSchedule.startBy a g 0#usize
      (Array.repeat 8#usize 0#u64) = .ok limbs0 := by
    change AspisR1FastDotsOuterFoldTraceV2.Outer
      (AspisR1FastDotsOuterFoldTraceV2.BatchOps
        (AspisR1FastDotsOuterFoldTraceV2.LimbOps ops))
      AspisR1FastDotsStepSchedule.startBy a g 0#usize
      (Array.repeat 8#usize 0#u64) = .ok limbs0
    exact hloopActual
  obtain ⟨ds,starts,htrace,hseven,hlimits,hres⟩ :=
    AspisR1FastDotsOuterFoldTraceV2.actual_outer_success_reducer_residue
      ops a g 0#usize limbs0 hcoords houter
  obtain ⟨w0,w1,w2,w3,w4,w5,w6,w7,hi0,hi1,hi2,hi3,hi4,hi5,hi6,hi7,
      hresidues,hcanonical⟩ := actual_n8_array_success_residues ops limbs0 vals0 harray0
  have hidx0 := index_success_eq limbs0 0#usize w0 hi0
  have hidx1 := index_success_eq limbs0 1#usize w1 hi1
  have hidx2 := index_success_eq limbs0 2#usize w2 hi2
  have hidx3 := index_success_eq limbs0 3#usize w3 hi3
  have hidx4 := index_success_eq limbs0 4#usize w4 hi4
  have hidx5 := index_success_eq limbs0 5#usize w5 hi5
  have hidx6 := index_success_eq limbs0 6#usize w6 hi6
  have hidx7 := index_success_eq limbs0 7#usize w7 hi7
  have hword0 : w0.val % AspisV8R17.RawReducer.P =
      AspisR1.FastDotFoldedBatches.fullSum
        (AspisR1FastDotsOuterFoldTraceV2.rawBatchLists ds ⟨0,by decide⟩) %
        AspisR1BatchedFoldArithmetic.modulus := by
    obtain ⟨z,hred,hz,_⟩ := hres ⟨0,by decide⟩
    have hredCell := hred
    change AspisR1Qm31ArithmeticProbe.field.M31.reduce_u64 (limbs0.val[0]) = .ok z at hredCell
    have hidxCell := hidx0
    change w0 = limbs0.val[0] at hidxCell
    rw [← hidxCell] at hredCell
    have hcurrent :
        (AspisR1FastDotsCurrentM31OpsBinding.withCurrentM31ParserReducer
          (AspisR1FastDotsOuterFoldTraceV2.ActualOps ops)).m31ReduceU64 w0 = .ok z := by
      rw [AspisR1FastDotsCurrentM31OpsBinding.reducer_binding]
      exact hredCell
    have hmod := AspisR1FastDotsCurrentM31OpsBinding.reducer_success_mod
      (AspisR1FastDotsOuterFoldTraceV2.ActualOps ops) w0 z hcurrent
    rw [AspisR1BatchedFoldArithmetic.modulus]
    exact hmod.1.symm.trans hz
  have hword1 : w1.val % AspisV8R17.RawReducer.P =
      AspisR1.FastDotFoldedBatches.fullSum
        (AspisR1FastDotsOuterFoldTraceV2.rawBatchLists ds ⟨1,by decide⟩) %
        AspisR1BatchedFoldArithmetic.modulus := by
    obtain ⟨z,hred,hz,_⟩ := hres ⟨1,by decide⟩
    have hredCell := hred
    change AspisR1Qm31ArithmeticProbe.field.M31.reduce_u64 (limbs0.val[1]) = .ok z at hredCell
    have hidxCell := hidx1
    change w1 = limbs0.val[1] at hidxCell
    rw [← hidxCell] at hredCell
    have hcurrent :
        (AspisR1FastDotsCurrentM31OpsBinding.withCurrentM31ParserReducer
          (AspisR1FastDotsOuterFoldTraceV2.ActualOps ops)).m31ReduceU64 w1 = .ok z := by
      rw [AspisR1FastDotsCurrentM31OpsBinding.reducer_binding]
      exact hredCell
    have hmod := AspisR1FastDotsCurrentM31OpsBinding.reducer_success_mod
      (AspisR1FastDotsOuterFoldTraceV2.ActualOps ops) w1 z hcurrent
    rw [AspisR1BatchedFoldArithmetic.modulus]
    exact hmod.1.symm.trans hz
  have hword2 : w2.val % AspisV8R17.RawReducer.P =
      AspisR1.FastDotFoldedBatches.fullSum
        (AspisR1FastDotsOuterFoldTraceV2.rawBatchLists ds ⟨2,by decide⟩) %
        AspisR1BatchedFoldArithmetic.modulus := by
    obtain ⟨z,hred,hz,_⟩ := hres ⟨2,by decide⟩
    have hredCell := hred
    change AspisR1Qm31ArithmeticProbe.field.M31.reduce_u64 (limbs0.val[2]) = .ok z at hredCell
    have hidxCell := hidx2
    change w2 = limbs0.val[2] at hidxCell
    rw [← hidxCell] at hredCell
    have hcurrent :
        (AspisR1FastDotsCurrentM31OpsBinding.withCurrentM31ParserReducer
          (AspisR1FastDotsOuterFoldTraceV2.ActualOps ops)).m31ReduceU64 w2 = .ok z := by
      rw [AspisR1FastDotsCurrentM31OpsBinding.reducer_binding]
      exact hredCell
    have hmod := AspisR1FastDotsCurrentM31OpsBinding.reducer_success_mod
      (AspisR1FastDotsOuterFoldTraceV2.ActualOps ops) w2 z hcurrent
    rw [AspisR1BatchedFoldArithmetic.modulus]
    exact hmod.1.symm.trans hz
  have hword3 : w3.val % AspisV8R17.RawReducer.P =
      AspisR1.FastDotFoldedBatches.fullSum
        (AspisR1FastDotsOuterFoldTraceV2.rawBatchLists ds ⟨3,by decide⟩) %
        AspisR1BatchedFoldArithmetic.modulus := by
    obtain ⟨z,hred,hz,_⟩ := hres ⟨3,by decide⟩
    have hredCell := hred
    change AspisR1Qm31ArithmeticProbe.field.M31.reduce_u64 (limbs0.val[3]) = .ok z at hredCell
    have hidxCell := hidx3
    change w3 = limbs0.val[3] at hidxCell
    rw [← hidxCell] at hredCell
    have hcurrent :
        (AspisR1FastDotsCurrentM31OpsBinding.withCurrentM31ParserReducer
          (AspisR1FastDotsOuterFoldTraceV2.ActualOps ops)).m31ReduceU64 w3 = .ok z := by
      rw [AspisR1FastDotsCurrentM31OpsBinding.reducer_binding]
      exact hredCell
    have hmod := AspisR1FastDotsCurrentM31OpsBinding.reducer_success_mod
      (AspisR1FastDotsOuterFoldTraceV2.ActualOps ops) w3 z hcurrent
    rw [AspisR1BatchedFoldArithmetic.modulus]
    exact hmod.1.symm.trans hz
  have hword4 : w4.val % AspisV8R17.RawReducer.P =
      AspisR1.FastDotFoldedBatches.fullSum
        (AspisR1FastDotsOuterFoldTraceV2.rawBatchLists ds ⟨4,by decide⟩) %
        AspisR1BatchedFoldArithmetic.modulus := by
    obtain ⟨z,hred,hz,_⟩ := hres ⟨4,by decide⟩
    have hredCell := hred
    change AspisR1Qm31ArithmeticProbe.field.M31.reduce_u64 (limbs0.val[4]) = .ok z at hredCell
    have hidxCell := hidx4
    change w4 = limbs0.val[4] at hidxCell
    rw [← hidxCell] at hredCell
    have hcurrent :
        (AspisR1FastDotsCurrentM31OpsBinding.withCurrentM31ParserReducer
          (AspisR1FastDotsOuterFoldTraceV2.ActualOps ops)).m31ReduceU64 w4 = .ok z := by
      rw [AspisR1FastDotsCurrentM31OpsBinding.reducer_binding]
      exact hredCell
    have hmod := AspisR1FastDotsCurrentM31OpsBinding.reducer_success_mod
      (AspisR1FastDotsOuterFoldTraceV2.ActualOps ops) w4 z hcurrent
    rw [AspisR1BatchedFoldArithmetic.modulus]
    exact hmod.1.symm.trans hz
  have hword5 : w5.val % AspisV8R17.RawReducer.P =
      AspisR1.FastDotFoldedBatches.fullSum
        (AspisR1FastDotsOuterFoldTraceV2.rawBatchLists ds ⟨5,by decide⟩) %
        AspisR1BatchedFoldArithmetic.modulus := by
    obtain ⟨z,hred,hz,_⟩ := hres ⟨5,by decide⟩
    have hredCell := hred
    change AspisR1Qm31ArithmeticProbe.field.M31.reduce_u64 (limbs0.val[5]) = .ok z at hredCell
    have hidxCell := hidx5
    change w5 = limbs0.val[5] at hidxCell
    rw [← hidxCell] at hredCell
    have hcurrent :
        (AspisR1FastDotsCurrentM31OpsBinding.withCurrentM31ParserReducer
          (AspisR1FastDotsOuterFoldTraceV2.ActualOps ops)).m31ReduceU64 w5 = .ok z := by
      rw [AspisR1FastDotsCurrentM31OpsBinding.reducer_binding]
      exact hredCell
    have hmod := AspisR1FastDotsCurrentM31OpsBinding.reducer_success_mod
      (AspisR1FastDotsOuterFoldTraceV2.ActualOps ops) w5 z hcurrent
    rw [AspisR1BatchedFoldArithmetic.modulus]
    exact hmod.1.symm.trans hz
  have hword6 : w6.val % AspisV8R17.RawReducer.P =
      AspisR1.FastDotFoldedBatches.fullSum
        (AspisR1FastDotsOuterFoldTraceV2.rawBatchLists ds ⟨6,by decide⟩) %
        AspisR1BatchedFoldArithmetic.modulus := by
    obtain ⟨z,hred,hz,_⟩ := hres ⟨6,by decide⟩
    have hredCell := hred
    change AspisR1Qm31ArithmeticProbe.field.M31.reduce_u64 (limbs0.val[6]) = .ok z at hredCell
    have hidxCell := hidx6
    change w6 = limbs0.val[6] at hidxCell
    rw [← hidxCell] at hredCell
    have hcurrent :
        (AspisR1FastDotsCurrentM31OpsBinding.withCurrentM31ParserReducer
          (AspisR1FastDotsOuterFoldTraceV2.ActualOps ops)).m31ReduceU64 w6 = .ok z := by
      rw [AspisR1FastDotsCurrentM31OpsBinding.reducer_binding]
      exact hredCell
    have hmod := AspisR1FastDotsCurrentM31OpsBinding.reducer_success_mod
      (AspisR1FastDotsOuterFoldTraceV2.ActualOps ops) w6 z hcurrent
    rw [AspisR1BatchedFoldArithmetic.modulus]
    exact hmod.1.symm.trans hz
  have hword7 : w7.val % AspisV8R17.RawReducer.P =
      AspisR1.FastDotFoldedBatches.fullSum
        (AspisR1FastDotsOuterFoldTraceV2.rawBatchLists ds ⟨7,by decide⟩) %
        AspisR1BatchedFoldArithmetic.modulus := by
    obtain ⟨z,hred,hz,_⟩ := hres ⟨7,by decide⟩
    have hredCell := hred
    change AspisR1Qm31ArithmeticProbe.field.M31.reduce_u64 (limbs0.val[7]) = .ok z at hredCell
    have hidxCell := hidx7
    change w7 = limbs0.val[7] at hidxCell
    rw [← hidxCell] at hredCell
    have hcurrent :
        (AspisR1FastDotsCurrentM31OpsBinding.withCurrentM31ParserReducer
          (AspisR1FastDotsOuterFoldTraceV2.ActualOps ops)).m31ReduceU64 w7 = .ok z := by
      rw [AspisR1FastDotsCurrentM31OpsBinding.reducer_binding]
      exact hredCell
    have hmod := AspisR1FastDotsCurrentM31OpsBinding.reducer_success_mod
      (AspisR1FastDotsOuterFoldTraceV2.ActualOps ops) w7 z hcurrent
    rw [AspisR1BatchedFoldArithmetic.modulus]
    exact hmod.1.symm.trans hz
  refine ⟨v0,v1,v2,v3,limbs0,limbs1,limbs2,limbs3,vals0,vals1,vals2,vals3,ds,starts,
    hvalues,hloop0,harray0,htrace,hseven,?_,hcanonical⟩
  rw [hresidues,hword0,hword1,hword2,hword3,hword4,hword5,hword6,hword7]

#print axioms generatedFourDotsSlot0_success_actual_n8_batch_residue
end AspisR1FastDotsOuterN8BatchResidueV2
