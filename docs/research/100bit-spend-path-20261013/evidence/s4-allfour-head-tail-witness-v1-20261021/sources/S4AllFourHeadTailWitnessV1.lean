import S4FromFnP6OuterSameClosureLoop0V1
import S4HeadTailSharedWitnessRootV2
import S4ConcreteTailInstallRootV1
import S4TailWideAddCurrentV1

open Aeneas Aeneas.Std Result AspisR1FastDotsCurrent
set_option autoImplicit false

namespace AspisR1FastDotsAllFourHeadTailWitnessV1

abbrev Ops := AspisR1FastDotsCurrent.FourDotsOps
abbrev Wide := AspisR1FastDotsCurrent.aspis_core.field.wide_exact.WideExact
abbrev U8 := Std.U8
abbrev Closure := AspisR1FastDotsActualCallbackTailTraceRootV1.Closure
abbrev Outer := AspisR1FromFnP6Generated.fourDotsOpsWithP6ArrayFromFnN4N8
abbrev ActualBatchOps := AspisR1FastDotsOuterN8BatchResidueV2.ActualOps
abbrev U64 := Std.U64
abbrev U32 := Std.U32

def outerOps (base : Ops) : Ops := Outer (ActualBatchOps (AspisR1FastDotsConcreteTailInstallRootV1.install base))

private theorem install_outerOps (base : Ops) :
    AspisR1FastDotsConcreteTailInstallRootV1.install (outerOps base) = outerOps base := by
  cases base <;> rfl

/-- The complete witnesses returned by the same successful generated callback
    decomposition.  This packages the exact `BaseLoop`, N8 array call, packed
    body, source tail trace, accepted product trace, final addition and decoded
    addition without introducing independent child-run premises. -/
def CallbackWitness (ops : Ops) (a : Array U8 608#usize)
    (g : Array Wide 29#usize) (slot : Usize) (value : Wide) : Prop :=
  ∃ iter limbs body vals wide28 q tailStart tail2 tailValue cs,
    core.iter.traits.iterator.Iterator.step_by.trait_default
      (core.iter.traits.iterator.IteratorRange core.iter.range.StepUsize)
      {start:=0#usize, «end»:=26#usize} 4#usize = .ok iter ∧
    AspisR1FastDotsActualCallbackTailTraceRootV1.BaseLoop ops iter a g slot
      (Array.repeat 8#usize 0#u64) = .ok limbs ∧
    ops.arrayFromFn 8#usize
      (AspisR1FastDotsCurrent.fast_dots.four_dots.closure.closure.Insts.CoreOpsFunctionFnMutTupleUsizeU32 ops)
      limbs = .ok vals ∧
    Array.index_usize g 28#usize = .ok wide28 ∧
    AspisR1FastDotsHeadTailSharedWitnessRootV2.FirstQueryInput ops a slot q ∧
    ops.wideFromLimbs vals = .ok (some body) ∧
    ops.ebyKNew = .ok EbyKNewToPushStateABI.pushZero ∧
    ops.ebyKPush EbyKNewToPushStateABI.pushZero wide28 q = .ok (.Ok (),tailStart) ∧
    AspisR1FastDotsActualTailLoopTraceRootV1.RunTrace ops a g slot
      {start:=0#usize, «end»:=2#usize} tailStart tail2 cs ∧
    ops.ebyKFinish tail2 = .ok tailValue ∧
    ops.wideAdd body tailValue = .ok value ∧
    cs.map (fun c => c.term.val) = [0,1] ∧ cs.length = 2 ∧
    AspisR1DotCountBoundV1.AcceptedPushTrace
      AspisR1FastDotsPushProductTraceRootV1.raw EbyKNewToPushStateABI.pushZero
      ((wide28,q)::cs.map (fun c => (c.coefficient,c.scalar))) tail2 ∧
    AspisR1FastDotsPushProductTraceRootV1.stateValue tail2 =
      ((wide28,q)::cs.map (fun c => (c.coefficient,c.scalar))).foldl
        AspisR1FastDotsPushProductTraceRootV1.addProduct
        (AspisR1FastDotsPushProductTraceRootV1.stateValue EbyKNewToPushStateABI.pushZero) ∧
    AspisR1CurrentWide.Proof.CanonicalWide (AspisR1FastDotsTailWideAddCurrentV1.s4ToCurrentE value) ∧
    AspisR1CurrentWide.Proof.decodeWide (AspisR1FastDotsTailWideAddCurrentV1.s4ToCurrentE value) =
      AspisR1CurrentWide.Proof.decodeWide (AspisR1FastDotsTailWideAddCurrentV1.s4ToCurrentE body) +
      AspisR1CurrentWide.Proof.decodeWide (AspisR1FastDotsTailWideAddCurrentV1.s4ToCurrentE tailValue) ∧
    (AspisR1FastDotsTailFinishSourceMapV1.currentFinishWords tailValue).map (fun w => w.val) =
      ((tail2.c0.sums.val ++ tail2.c1.sums.val).map
        (fun x => x.val % AspisV8R17.RawReducer.P))

/-- One successful N=4 generated constructor call gives all four full callback
    traces on the same captured `(q,g)` and slots `0,1,2,3`.  The generated
    array/fnMut execution still carries the explicitly documented P6/std
    correspondence boundary. -/
theorem generatedFourDotsN4_success_all_four_head_tail_witnesses
    (base : Ops) (a : Array U8 608#usize) (g : Array Wide 29#usize)
    (hcoords : ∀ i : Fin 29,
      AspisR1FastDotsHeadTailSharedWitnessRootV2.CoordBound
        (g.val[i.val]'(by simpa [g.property] using i.isLt)))
    {values : Array Wide 4#usize}
    (h : (outerOps base).arrayFromFn 4#usize
      (AspisR1FastDotsCurrent.fast_dots.four_dots.closure.Insts.CoreOpsFunctionFnMutTupleUsizeWideExact
        (outerOps base)) (a,g) = .ok values) :
    ∃ v0 v1 v2 v3 : Wide,
      values.val = [v0,v1,v2,v3] ∧
      CallbackWitness (AspisR1FastDotsConcreteTailInstallRootV1.install (outerOps base))
        a g 0#usize v0 ∧
      CallbackWitness (AspisR1FastDotsConcreteTailInstallRootV1.install (outerOps base))
        a g 1#usize v1 ∧
      CallbackWitness (AspisR1FastDotsConcreteTailInstallRootV1.install (outerOps base))
        a g 2#usize v2 ∧
      CallbackWitness (AspisR1FastDotsConcreteTailInstallRootV1.install (outerOps base))
        a g 3#usize v3 := by
  obtain ⟨v0,v1,v2,v3,_limbs0,_limbs1,_limbs2,_limbs3,_vals0,_vals1,_vals2,_vals3,
      hvalues,hcall0,hcall1,hcall2,hcall3,_hstep,_hloop0,_harray0,_hloop1,_harray1,
      _hloop2,_harray2,_hloop3,_harray3⟩ :=
    AspisR1FromFnP6Generated.generatedFourDotsN4_success_same_closure_loop0_four_calls
      (ActualBatchOps (AspisR1FastDotsConcreteTailInstallRootV1.install base)) a g h
  have hcall0' : AspisR1FastDotsActualCallbackTailTraceRootV1.Callback
      (AspisR1FastDotsConcreteTailInstallRootV1.install (outerOps base)) (a,g) 0#usize =
        .ok (v0,(a,g)) := by rw [install_outerOps]; exact hcall0
  have hcall1' : AspisR1FastDotsActualCallbackTailTraceRootV1.Callback
      (AspisR1FastDotsConcreteTailInstallRootV1.install (outerOps base)) (a,g) 1#usize =
        .ok (v1,(a,g)) := by rw [install_outerOps]; exact hcall1
  have hcall2' : AspisR1FastDotsActualCallbackTailTraceRootV1.Callback
      (AspisR1FastDotsConcreteTailInstallRootV1.install (outerOps base)) (a,g) 2#usize =
        .ok (v2,(a,g)) := by rw [install_outerOps]; exact hcall2
  have hcall3' : AspisR1FastDotsActualCallbackTailTraceRootV1.Callback
      (AspisR1FastDotsConcreteTailInstallRootV1.install (outerOps base)) (a,g) 3#usize =
        .ok (v3,(a,g)) := by rw [install_outerOps]; exact hcall3
  have h0 := AspisR1FastDotsHeadTailSharedWitnessRootV2.installed_callback_head_tail_product_value
    (outerOps base) a g 0#usize v0 (a,g) hcoords hcall0'
  have h1 := AspisR1FastDotsHeadTailSharedWitnessRootV2.installed_callback_head_tail_product_value
    (outerOps base) a g 1#usize v1 (a,g) hcoords hcall1'
  have h2 := AspisR1FastDotsHeadTailSharedWitnessRootV2.installed_callback_head_tail_product_value
    (outerOps base) a g 2#usize v2 (a,g) hcoords hcall2'
  have h3 := AspisR1FastDotsHeadTailSharedWitnessRootV2.installed_callback_head_tail_product_value
    (outerOps base) a g 3#usize v3 (a,g) hcoords hcall3'
  exact ⟨v0,v1,v2,v3,hvalues,h0,h1,h2,h3⟩

#print axioms generatedFourDotsN4_success_all_four_head_tail_witnesses

end AspisR1FastDotsAllFourHeadTailWitnessV1
