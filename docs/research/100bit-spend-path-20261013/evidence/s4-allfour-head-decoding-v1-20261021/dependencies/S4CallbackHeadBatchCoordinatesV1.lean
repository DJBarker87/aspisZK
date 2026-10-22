import S4OuterN8BatchResidueV2
import S4N8WideFromLimbsABI
import S4N8WideFromLimbsCallBridgeV1
import FourDotsActualCallbackTailTraceRootV1
import FourDotsActualSevenBatchLimbBoundV2
import S4FromFnP6GeneratedTrace

open Aeneas Aeneas.Std Result AspisR1FastDotsCurrent AspisR1FromFnP6Generated
set_option autoImplicit false

namespace AspisR1FastDotsCallbackHeadBatchCoordinatesV1

abbrev Ops := AspisR1FastDotsCurrent.FourDotsOps
abbrev Wide := AspisR1FastDotsCurrent.aspis_core.field.wide_exact.WideExact
abbrev U8 := Std.U8
abbrev U64 := Std.U64
abbrev U32 := Std.U32
abbrev Callback := AspisR1FastDotsCurrent.fast_dots.four_dots.closure.Insts.CoreOpsFunctionFnMutTupleUsizeWideExact.call_mut
abbrev InnerFn (ops : Ops) :=
  AspisR1FastDotsCurrent.fast_dots.four_dots.closure.closure.Insts.CoreOpsFunctionFnMutTupleUsizeU32 ops
abbrev ActualBatchOps := AspisR1FastDotsOuterN8BatchResidueV2.ActualOps
abbrev BaseLoop := AspisR1FastDotsActualCallbackTailTraceRootV1.BaseLoop
abbrev SlotBatchOutput := AspisR1FastDotsOuterN8BatchResidueV2.SlotBatchOutput

/-- Explicit P6/current-reducer model for the source callback's N8 array call,
    together with the checked EbyK `from_limbs` operation. The Std/P6 and Rust
    operation-installation correspondences remain explicit boundaries. -/
def headOps (ops : Ops) : Ops :=
  AspisR1FastDotsN8WideFromLimbsABI.withCurrentFromLimbs
    (AspisR1FromFnP6Generated.fourDotsOpsWithP6ArrayFromFnN4N8
      (ActualBatchOps ops))

/-- One successful generated callback call retains the same base accumulator,
    actual N8 array result and actual seven-batch source trace. Each returned
    array word is the residue of the exact source products in that trace, and
    the callback's packed body is precisely the eight returned words. -/
theorem actual_callback_head_batch_coordinates
    (ops : Ops) (a : Array U8 608#usize) (g : Array Wide 29#usize)
    (slot : Usize)
    (hcoords : ∀ i : Fin 29,
      AspisR1FastDotsWideLimbCanonical.CoordinateBound
        (g.val[i.val]'(by simpa [g.property] using i.isLt)))
    (value : Wide) (c' : AspisR1FastDotsCurrent.fast_dots.four_dots.closure)
    (h : Callback (headOps ops) (a,g) slot = .ok (value,c')) :
    ∃ (iter : AspisR1FastDotsActualCallbackTailTraceRootV1.StepBy)
      (limbs : Array U64 8#usize) (values : Array U32 8#usize)
      (body : Wide) (ds : List (List AspisR1FastDotsOuterFoldTraceV2.Contribution))
      (starts : List Nat),
      core.iter.traits.iterator.Iterator.step_by.trait_default
        (core.iter.traits.iterator.IteratorRange core.iter.range.StepUsize)
        {start:=0#usize, «end»:=26#usize} 4#usize = .ok iter ∧
      BaseLoop (headOps ops) iter a g slot (Array.repeat 8#usize 0#u64) = .ok limbs ∧
      (headOps ops).arrayFromFn 8#usize (InnerFn (headOps ops)) limbs = .ok values ∧
      (headOps ops).wideFromLimbs values = .ok (some body) ∧
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
      (∀ x, x ∈ values.val → x.val < AspisV8R17.RawReducer.P) ∧
      body = AspisR1FastDotsN8WideFromLimbsABI.finishToCurrent
        (AspisR1EbyKFinish.Proof.wideFromParts
          (AspisR1FastDotsN8WideFromLimbsCallBridgeV1.word0 values)
          (AspisR1FastDotsN8WideFromLimbsCallBridgeV1.word1 values)
          (AspisR1FastDotsN8WideFromLimbsCallBridgeV1.word2 values)
          (AspisR1FastDotsN8WideFromLimbsCallBridgeV1.word3 values)
          (AspisR1FastDotsN8WideFromLimbsCallBridgeV1.word4 values)
          (AspisR1FastDotsN8WideFromLimbsCallBridgeV1.word5 values)
          (AspisR1FastDotsN8WideFromLimbsCallBridgeV1.word6 values)
          (AspisR1FastDotsN8WideFromLimbsCallBridgeV1.word7 values)) := by
  obtain ⟨_hc,iter,limbs,values,optBody,body,_tail0,_wide28,_slotOffset,
      _start,_finish,_bytes,_optQ,_q,_pushed,_u,_tail2,_tailValue,
      hstep,hbase,harray,hbody,hunwrap,_hnew,_hread,_hmul,_hadd104,_hadd120,
      _hslice,_hparse,_hunq,_hpush,_hunpush,_htail,_hfinish,_hadd⟩ :=
    AspisR1FastDotsActualCallbackTailTraceRootV1.actual_callback_success_base_and_tail
      (headOps ops) a g slot value c' h
  have hopt : optBody = some body := by
    have hu : Result.ofOption optBody Error.panic = .ok body := by
      change Result.ofOption optBody Error.panic = .ok body
      exact hunwrap
    cases optBody with
    | none => simp [Result.ofOption] at hu
    | some w => simp only [Result.ofOption, Result.ok.injEq] at hu; subst w; rfl
  have hbody' : (headOps ops).wideFromLimbs values = .ok (some body) := by
    rw [hopt] at hbody
    exact hbody
  have hbase0 := hbase
  change AspisR1FastDotsCurrent.fast_dots.four_dots.closure.Insts.CoreOpsFunctionFnMutTupleUsizeWideExact.call_mut_loop0
      (AspisR1FromFnP6Generated.fourDotsOpsWithP6ArrayFromFnN4N8
        (ActualBatchOps ops)) iter a g slot (Array.repeat 8#usize 0#u64) = .ok limbs at hbase0
  rw [AspisR1FromFnP6Generated.generatedLoop0_ignores_p6_array_adapter
    (ActualBatchOps ops) _ a g slot _] at hbase0
  have hstartEq := Result.ok.inj
    (hstep.symm.trans AspisR1FastDotsStepSchedule.initialized_step_by)
  have houter : AspisR1FastDotsOuterN8BatchResidueV2.Outer ops
      AspisR1FastDotsStepSchedule.startBy a g slot
      (Array.repeat 8#usize 0#u64) = .ok limbs := by
    change AspisR1FastDotsCurrent.fast_dots.four_dots.closure.Insts.CoreOpsFunctionFnMutTupleUsizeWideExact.call_mut_loop0
      (ActualBatchOps ops) iter a g slot (Array.repeat 8#usize 0#u64) = .ok limbs at hbase0
    simpa only [hstartEq] using hbase0
  have harray0 : (AspisR1FromFnP6Generated.fourDotsOpsWithP6ArrayFromFnN4N8
      (ActualBatchOps ops)).arrayFromFn 8#usize
      (InnerFn (AspisR1FromFnP6Generated.fourDotsOpsWithP6ArrayFromFnN4N8
        (ActualBatchOps ops))) limbs = .ok values := by
    change (headOps ops).arrayFromFn 8#usize (InnerFn (headOps ops)) limbs = .ok values
    exact harray
  obtain ⟨_ho,_ha,⟨ds,starts,htrace,hseven,hmap,hcanonical⟩⟩ :=
    AspisR1FastDotsOuterN8BatchResidueV2.actual_n8_batch_residue_from_calls_output
      ops a g slot hcoords limbs values houter harray0
  have hpack := AspisR1FastDotsN8WideFromLimbsABI.actual_wideFromLimbs_of_canonical_words
    (headOps ops) values body hcanonical
    (by intro xs; rfl) hbody'
  exact ⟨iter,limbs,values,body,ds,starts,hstep,hbase,harray,hbody',htrace,hseven,
    hmap,hcanonical,hpack⟩

#print axioms actual_callback_head_batch_coordinates

end AspisR1FastDotsCallbackHeadBatchCoordinatesV1
