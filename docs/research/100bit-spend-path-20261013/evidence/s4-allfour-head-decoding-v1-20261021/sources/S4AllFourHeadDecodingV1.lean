import S4AllFourHeadTailWitnessV1
import S4CallbackHeadBatchCoordinatesV1

open Aeneas Aeneas.Std Result AspisR1FastDotsCurrent
set_option autoImplicit false

namespace AspisR1FastDotsAllFourHeadDecodingV1

abbrev Ops := AspisR1FastDotsCurrent.FourDotsOps
abbrev Wide := AspisR1FastDotsCurrent.aspis_core.field.wide_exact.WideExact
abbrev U8 := Std.U8
abbrev U64 := Std.U64
abbrev U32 := Std.U32
def Outer (ops : Ops) := AspisR1FastDotsAllFourHeadTailWitnessV1.outerOps ops
def HeadOps (ops : Ops) := AspisR1FastDotsCallbackHeadBatchCoordinatesV1.headOps ops

private theorem outerOp_eq (base : Ops) :
    Outer base = AspisR1FromFnP6Generated.fourDotsOpsWithP6ArrayFromFnN4N8
      (AspisR1FastDotsOuterN8BatchResidueV2.ActualOps
        (AspisR1FastDotsConcreteTailInstallRootV1.install base)) := rfl

private theorem headOps_eq_outer (base : Ops) :
    AspisR1FastDotsCallbackHeadBatchCoordinatesV1.headOps
      (AspisR1FastDotsConcreteTailInstallRootV1.install base) = Outer base := rfl

/-- The head facts are proved from the same callback call as the full head/tail
    witness. In particular, the N8 array and batch trace are not independent
    successful-run premises. -/
def SlotHeadWitness (ops : Ops) (a : Array U8 608#usize)
    (g : Array Wide 29#usize) (slot : Usize) (value : Wide) : Prop :=
  ∃ iter : AspisR1FastDotsActualCallbackTailTraceRootV1.StepBy,
    ∃ limbs : Array U64 8#usize, ∃ values : Array U32 8#usize,
    ∃ body : Wide, ∃ ds : List (List AspisR1FastDotsOuterFoldTraceV2.Contribution),
    ∃ starts : List Nat,
    core.iter.traits.iterator.Iterator.step_by.trait_default
      (core.iter.traits.iterator.IteratorRange core.iter.range.StepUsize)
      {start:=0#usize, «end»:=26#usize} 4#usize = .ok iter ∧
    AspisR1FastDotsActualCallbackTailTraceRootV1.BaseLoop (HeadOps (AspisR1FastDotsConcreteTailInstallRootV1.install ops))
      iter a g slot (Array.repeat 8#usize 0#u64) = .ok limbs ∧
    (HeadOps (AspisR1FastDotsConcreteTailInstallRootV1.install ops)).arrayFromFn
      8#usize
      (AspisR1FastDotsCallbackHeadBatchCoordinatesV1.InnerFn
        (HeadOps (AspisR1FastDotsConcreteTailInstallRootV1.install ops))) limbs = .ok values ∧
    (HeadOps (AspisR1FastDotsConcreteTailInstallRootV1.install ops)).wideFromLimbs values = .ok (some body) ∧
    AspisR1FastDotsOuterFoldTraceV2.ExactTrace
      (AspisR1FastDotsConcreteTailInstallRootV1.install ops) a g slot
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
        (AspisR1FastDotsN8WideFromLimbsCallBridgeV1.word7 values))

/-- One successful outer generated N=4 call yields four exact source-head
    N8 residue/packing witnesses for the same captured inputs and callback
    executions retained by `CallbackWitness`. -/
theorem generatedFourDotsN4_success_all_four_head_decodings
    (base : Ops) (a : Array U8 608#usize) (g : Array Wide 29#usize)
    (hcoords : ∀ i : Fin 29,
      AspisR1FastDotsHeadTailSharedWitnessRootV2.CoordBound
        (g.val[i.val]'(by simpa [g.property] using i.isLt)))
    {values : Array Wide 4#usize}
    (h : (Outer base).arrayFromFn 4#usize
      (AspisR1FastDotsCurrent.fast_dots.four_dots.closure.Insts.CoreOpsFunctionFnMutTupleUsizeWideExact
        (Outer base)) (a,g) = .ok values) :
    ∃ v0 v1 v2 v3 : Wide,
      values.val = [v0,v1,v2,v3] ∧
      AspisR1FastDotsAllFourHeadTailWitnessV1.CallbackWitness
        (AspisR1FastDotsConcreteTailInstallRootV1.install (Outer base)) a g 0#usize v0 ∧
      AspisR1FastDotsAllFourHeadTailWitnessV1.CallbackWitness
        (AspisR1FastDotsConcreteTailInstallRootV1.install (Outer base)) a g 1#usize v1 ∧
      AspisR1FastDotsAllFourHeadTailWitnessV1.CallbackWitness
        (AspisR1FastDotsConcreteTailInstallRootV1.install (Outer base)) a g 2#usize v2 ∧
      AspisR1FastDotsAllFourHeadTailWitnessV1.CallbackWitness
        (AspisR1FastDotsConcreteTailInstallRootV1.install (Outer base)) a g 3#usize v3 ∧
      SlotHeadWitness base a g 0#usize v0 ∧
      SlotHeadWitness base a g 1#usize v1 ∧
      SlotHeadWitness base a g 2#usize v2 ∧
      SlotHeadWitness base a g 3#usize v3 := by
  obtain ⟨v0,v1,v2,v3,hvalues,hw0,hw1,hw2,hw3⟩ :=
    AspisR1FastDotsAllFourHeadTailWitnessV1.generatedFourDotsN4_success_all_four_head_tail_witnesses
      base a g (by intro i; exact hcoords i) h
  obtain ⟨v0',v1',v2',v3',_limbs0,_limbs1,_limbs2,_limbs3,_vals0,_vals1,_vals2,_vals3,
      hvalues',hcall0,hcall1,hcall2,hcall3,_hstep,_hloop0,_harray0,_hloop1,_harray1,
      _hloop2,_harray2,_hloop3,_harray3⟩ :=
    AspisR1FromFnP6Generated.generatedFourDotsN4_success_same_closure_loop0_four_calls
      (AspisR1FastDotsOuterN8BatchResidueV2.ActualOps
        (AspisR1FastDotsConcreteTailInstallRootV1.install base)) a g h
  have hvlist : [v0',v1',v2',v3'] = [v0,v1,v2,v3] := hvalues'.symm.trans hvalues
  have hparts := List.cons.inj hvlist
  have hv0 : v0' = v0 := hparts.1
  have hvrest : [v1',v2',v3'] = [v1,v2,v3] := hparts.2
  have hparts' := List.cons.inj hvrest
  have hv1 : v1' = v1 := hparts'.1
  have hvrest' : [v2',v3'] = [v2,v3] := hparts'.2
  have hparts'' := List.cons.inj hvrest'
  have hv2 : v2' = v2 := hparts''.1
  have hv3 : v3' = v3 := by simpa using hparts''.2
  have hcall0' : AspisR1FastDotsActualCallbackTailTraceRootV1.Callback
      (Outer base) (a,g) 0#usize = .ok (v0,(a,g)) := by
    rw [outerOp_eq]
    simpa only [hv0] using hcall0
  have hcall1' : AspisR1FastDotsActualCallbackTailTraceRootV1.Callback
      (Outer base) (a,g) 1#usize = .ok (v1,(a,g)) := by
    rw [outerOp_eq]
    simpa only [hv1] using hcall1
  have hcall2' : AspisR1FastDotsActualCallbackTailTraceRootV1.Callback
      (Outer base) (a,g) 2#usize = .ok (v2,(a,g)) := by
    rw [outerOp_eq]
    simpa only [hv2] using hcall2
  have hcall3' : AspisR1FastDotsActualCallbackTailTraceRootV1.Callback
      (Outer base) (a,g) 3#usize = .ok (v3,(a,g)) := by
    rw [outerOp_eq]
    simpa only [hv3] using hcall3
  have hcall0head : AspisR1FastDotsActualCallbackTailTraceRootV1.Callback
      (AspisR1FastDotsCallbackHeadBatchCoordinatesV1.headOps
        (AspisR1FastDotsConcreteTailInstallRootV1.install base))
      (a,g) 0#usize = .ok (v0,(a,g)) := by rw [headOps_eq_outer]; exact hcall0'
  have hcall1head : AspisR1FastDotsActualCallbackTailTraceRootV1.Callback
      (AspisR1FastDotsCallbackHeadBatchCoordinatesV1.headOps
        (AspisR1FastDotsConcreteTailInstallRootV1.install base))
      (a,g) 1#usize = .ok (v1,(a,g)) := by rw [headOps_eq_outer]; exact hcall1'
  have hcall2head : AspisR1FastDotsActualCallbackTailTraceRootV1.Callback
      (AspisR1FastDotsCallbackHeadBatchCoordinatesV1.headOps
        (AspisR1FastDotsConcreteTailInstallRootV1.install base))
      (a,g) 2#usize = .ok (v2,(a,g)) := by rw [headOps_eq_outer]; exact hcall2'
  have hcall3head : AspisR1FastDotsActualCallbackTailTraceRootV1.Callback
      (AspisR1FastDotsCallbackHeadBatchCoordinatesV1.headOps
        (AspisR1FastDotsConcreteTailInstallRootV1.install base))
      (a,g) 3#usize = .ok (v3,(a,g)) := by rw [headOps_eq_outer]; exact hcall3'
  have hcoords' : ∀ i : Fin 29,
      AspisR1FastDotsWideLimbCanonical.CoordinateBound
        (g.val[i.val]'(by simpa [g.property] using i.isLt)) := by
    intro i
    exact hcoords i
  have h0raw := AspisR1FastDotsCallbackHeadBatchCoordinatesV1.actual_callback_head_batch_coordinates
    (AspisR1FastDotsConcreteTailInstallRootV1.install base) a g 0#usize hcoords' v0
    (a,g) hcall0head
  have h1raw := AspisR1FastDotsCallbackHeadBatchCoordinatesV1.actual_callback_head_batch_coordinates
    (AspisR1FastDotsConcreteTailInstallRootV1.install base) a g 1#usize hcoords' v1
    (a,g) hcall1head
  have h2raw := AspisR1FastDotsCallbackHeadBatchCoordinatesV1.actual_callback_head_batch_coordinates
    (AspisR1FastDotsConcreteTailInstallRootV1.install base) a g 2#usize hcoords' v2
    (a,g) hcall2head
  have h3raw := AspisR1FastDotsCallbackHeadBatchCoordinatesV1.actual_callback_head_batch_coordinates
    (AspisR1FastDotsConcreteTailInstallRootV1.install base) a g 3#usize hcoords' v3
    (a,g) hcall3head
  -- The output identifiers above are pinned by the same four callback proofs.
  exact ⟨v0,v1,v2,v3,hvalues,hw0,hw1,hw2,hw3,by
    rcases h0raw with ⟨iter,limbs,vals,body,ds,starts,hstep,hbase,harray,hbody,htrace,hseven,hmap,hcanon,hpack⟩
    exact ⟨iter,limbs,vals,body,ds,starts,hstep,hbase,harray,hbody,htrace,hseven,hmap,hcanon,hpack⟩,
    by rcases h1raw with ⟨iter,limbs,vals,body,ds,starts,hstep,hbase,harray,hbody,htrace,hseven,hmap,hcanon,hpack⟩; exact ⟨iter,limbs,vals,body,ds,starts,hstep,hbase,harray,hbody,htrace,hseven,hmap,hcanon,hpack⟩,
    by rcases h2raw with ⟨iter,limbs,vals,body,ds,starts,hstep,hbase,harray,hbody,htrace,hseven,hmap,hcanon,hpack⟩; exact ⟨iter,limbs,vals,body,ds,starts,hstep,hbase,harray,hbody,htrace,hseven,hmap,hcanon,hpack⟩,
    by rcases h3raw with ⟨iter,limbs,vals,body,ds,starts,hstep,hbase,harray,hbody,htrace,hseven,hmap,hcanon,hpack⟩; exact ⟨iter,limbs,vals,body,ds,starts,hstep,hbase,harray,hbody,htrace,hseven,hmap,hcanon,hpack⟩⟩

#print axioms generatedFourDotsN4_success_all_four_head_decodings

end AspisR1FastDotsAllFourHeadDecodingV1
