import FourDotsActualTailInputMeaningRootV1
import FourDotsTailAcceptedTraceRootV1
import FourDotsPushProductTraceRootV1
import EbyKPowerValueCanonicalToPushV5
import S4TailCoefficientCanonicalV1
import S4FromLimbsSuccessCanonicalRootV1
set_option autoImplicit false
open Aeneas Aeneas.Std Result
namespace AspisR1FastDotsHeadTailSharedWitnessRootV1
open AspisR1FastDotsActualCallbackTailTraceRootV1
open AspisR1FastDotsActualTailBodyTraceRootV1 (Contribution)
open AspisR1FastDotsActualTailLoopTraceRootV1 (RunTrace)
open AspisR1FastDotsTailAcceptedTraceRootV1 (PushBinding)
abbrev Ops := AspisR1FastDotsActualCallbackTailTraceRootV1.Ops
abbrev Wide := AspisR1FastDotsActualCallbackTailTraceRootV1.Wide
abbrev QM := AspisR1FastDotsActualCallbackTailTraceRootV1.QM
abbrev Tail := AspisR1FastDotsActualCallbackTailTraceRootV1.Tail
abbrev Closure := AspisR1FastDotsActualCallbackTailTraceRootV1.Closure
abbrev Raw := AspisR1FastDotsTailAcceptedTraceRootV1.RawFn
abbrev PushCanonical := AspisR1EbyKPowerValueCanonicalToPush.pushCanonical
abbrev CoordBound := AspisR1FastDotsTailCoefficientCanonicalV1.CoordBound

private theorem unwrap_inner_success (r : core.result.Result Unit Unit) (u : Unit)
    (h : core.result.Result.unwrap core.fmt.DebugUnit r=.ok u) : r=.Ok () := by
  cases r with
  | Ok x => cases x; rfl
  | Err x => cases x; cases h

private theorem zero_sums_count_bound :
    AspisR1DotCountBoundV1.sumsBelowCount
      EbyKNewToPushStateABI.pushZero.count.val
      EbyKNewToPushStateABI.pushZero.c0.sums ∧
    AspisR1DotCountBoundV1.sumsBelowCount
      EbyKNewToPushStateABI.pushZero.count.val
      EbyKNewToPushStateABI.pushZero.c1.sums := by
  constructor <;> intro j hj <;>
    change ((List.replicate 4 (0#u64))[j]'hj).val≤0*2^34
  all_goals
    rw [List.getElem_replicate]
    exact Nat.le_refl 0

/-- The same successful emitted callback yields one accepted checked-push
    trace for the source coefficient and both actual tail iterations. Every
    coefficient is canonical from its exact source array read, so the checked
    push trace has the exact decoded product-sum state equation. This theorem
    keeps the concrete callback Ops, backend binding, and 29 source-coordinate
    bounds explicit; it does not assert the Rust std iterator/from_fn bridge. -/
theorem actual_callback_head_tail_product_trace
    (ops : Ops) (a : Array Std.U8 608#usize)
    (g : Array Wide 29#usize) (slot : Usize) (value : Wide) (closure' : Closure)
    (hcoords : ∀ j : Fin 29, CoordBound
      (g.val[j.val]'(by simpa [g.property] using j.isLt)))
    (hpushbinding : PushBinding ops AspisR1FastDotsPushProductTraceRootV1.raw)
    (hnewbinding : ops.ebyKNew=AspisR1FastDotsTailAcceptedTraceRootV1.newFromSource)
    (hcall : Callback ops (a,g) slot=.ok (value,closure')) :
    ∃ iter limbs body vals wide28 q tailStart tail2 tailValue cs,
      core.iter.traits.iterator.Iterator.step_by.trait_default
        (core.iter.traits.iterator.IteratorRange core.iter.range.StepUsize)
        {start:=0#usize, «end»:=26#usize} 4#usize = .ok iter ∧
      BaseLoop ops iter a g slot (Array.repeat 8#usize 0#u64) = .ok limbs ∧
      ops.arrayFromFn 8#usize
        (AspisR1FastDotsCurrent.fast_dots.four_dots.closure.closure.Insts.CoreOpsFunctionFnMutTupleUsizeU32 ops)
        limbs = .ok vals ∧
      Array.index_usize g 28#usize=.ok wide28 ∧
      ops.wideFromLimbs vals=.ok (some body) ∧
      ops.ebyKNew=.ok EbyKNewToPushStateABI.pushZero ∧
      ops.ebyKPush EbyKNewToPushStateABI.pushZero wide28 q=
        .ok (.Ok (),tailStart) ∧
      RunTrace ops a g slot {start:=0#usize, «end»:=2#usize}
        tailStart tail2 cs ∧
      AspisR1FastDotsActualCallbackTailTraceRootV1.TailLoop ops
        {start:=0#usize, «end»:=2#usize} a g slot tailStart = .ok tail2 ∧
      ops.ebyKFinish tail2 = .ok tailValue ∧
      ops.wideAdd body tailValue = .ok value ∧
      cs.map (fun c=>c.term.val)=[0,1] ∧ cs.length=2 ∧
      AspisR1DotCountBoundV1.AcceptedPushTrace AspisR1FastDotsPushProductTraceRootV1.raw
        EbyKNewToPushStateABI.pushZero
        ((wide28,q)::cs.map (fun c=>(c.coefficient,c.scalar))) tail2 ∧
      AspisR1FastDotsPushProductTraceRootV1.stateValue tail2 =
        ((wide28,q)::cs.map (fun c=>(c.coefficient,c.scalar))).foldl
          AspisR1FastDotsPushProductTraceRootV1.addProduct
          (AspisR1FastDotsPushProductTraceRootV1.stateValue
            EbyKNewToPushStateABI.pushZero) := by
  obtain ⟨hclosure,iter,limbs,vals,optBody,body,tail0,wide28,
    slotOffset,start,finish,bytes,optQ,q,pushed,u,tail2,tailValue,
    hstep,hbase,hvals,hbody,hunwrapBody,hnew,hread,hmul,hstart,hfinish,
    hslice,hparse,hunwrap,hpush,hunpush,hloop,hfinishTail,hadd⟩ :=
    actual_callback_success_base_and_tail ops a g slot value closure' hcall
  have htail0 : tail0=EbyKNewToPushStateABI.pushZero :=
    Result.ok.inj (hnew.symm.trans
      (hnewbinding.trans AspisR1FastDotsTailAcceptedTraceRootV1.newFromSource_zero))
  have hunwrap := unwrap_inner_success pushed.1 u hunpush
  have hpushed : pushed=(.Ok (),pushed.2) := Prod.ext hunwrap rfl
  have hsourcepush : ops.ebyKPush EbyKNewToPushStateABI.pushZero wide28 q=
      .ok (.Ok (),pushed.2) := by
    rw [htail0,hpushed] at hpush
    exact hpush
  have hfirst : AspisR1FastDotsTailAcceptedTraceRootV1.push AspisR1FastDotsPushProductTraceRootV1.raw
      EbyKNewToPushStateABI.pushZero wide28 q=.ok (.Ok (),pushed.2) := by
    rw [←hpushbinding]
    exact hsourcepush
  obtain ⟨cs,htrace,_hindices,_hlen⟩ :=
    AspisR1FastDotsActualTailLoopTraceRootV1.actual_two_term_tail_success_trace
      ops a g slot pushed.2 tail2 hloop
  have htail := AspisR1FastDotsTailAcceptedTraceRootV1.actual_tail_trace_checked_pushes
    ops AspisR1FastDotsPushProductTraceRootV1.raw a g slot _ pushed.2 tail2 cs hpushbinding htrace
  have hfull : AspisR1DotCountBoundV1.AcceptedPushTrace AspisR1FastDotsPushProductTraceRootV1.raw
      EbyKNewToPushStateABI.pushZero
      ((wide28,q)::cs.map (fun c=>(c.coefficient,c.scalar))) tail2 :=
    .cons _ pushed.2 tail2 wide28 q _ hfirst htail
  have hwidecanonical := AspisR1FastDotsTailCoefficientCanonicalV1.read_push_canonical
    g 28#usize wide28 hcoords hread
  have htailcanonical := AspisR1FastDotsTailCoefficientCanonicalV1.trace_coefficients_canonical
    ops a g slot {start:=0#usize, «end»:=2#usize} pushed.2 tail2 cs hcoords htrace
  have hallcanonical : ∀ p ∈ ((wide28,q)::cs.map (fun c=>(c.coefficient,c.scalar))),
      PushCanonical p.1 := by
    intro p hp
    rcases List.mem_cons.mp hp with hfirstmem | htailmem
    · cases hfirstmem
      exact hwidecanonical
    · rcases List.mem_map.mp htailmem with ⟨c,hc,rfl⟩
      exact htailcanonical c hc
  have hproduct := AspisR1FastDotsPushProductTraceRootV1.accepted_trace_product_sum
    EbyKNewToPushStateABI.pushZero tail2
    ((wide28,q)::cs.map (fun c=>(c.coefficient,c.scalar)))
    zero_sums_count_bound.1 zero_sums_count_bound.2 hallcanonical hfull
  have hoptBody : optBody=some body := by
    cases optBody with
    | none =>
      simp only [core.option.Option.unwrap, Result.ofOption] at hunwrapBody
      cases hunwrapBody
    | some b =>
      have hb : b=body := Result.ok.inj (by
        simpa only [core.option.Option.unwrap, Result.ofOption] using hunwrapBody)
      subst b
      rfl
  have hbodySome : ops.wideFromLimbs vals=.ok (some body) := by
    rw [←hoptBody]
    exact hbody
  have hnewzero : ops.ebyKNew=.ok EbyKNewToPushStateABI.pushZero := by
    rw [hnewbinding,AspisR1FastDotsTailAcceptedTraceRootV1.newFromSource_zero]
  exact ⟨iter,limbs,body,vals,wide28,q,pushed.2,tail2,tailValue,cs,hstep,hbase,hvals,hread,hbodySome,hnewzero,
    hsourcepush,htrace,hloop,hfinishTail,hadd,_hindices,_hlen,hfull,hproduct⟩

#print axioms actual_callback_head_tail_product_trace

open AspisR1FastDotsTailFinishSourceMapV1
open AspisR1FastDotsTailWideAddCurrentV1
open AspisR1FastDotsConcreteTailInstallRootV1

theorem finish_carrier_eq (f : AspisR1CurrentWide.Proof.FinishE) :
    s4ToCurrentE (finishEToCurrent f) = AspisR1CurrentWide.Proof.ofFinishE f := by
  cases f
  rfl

/-- All head and tail witnesses come from one emitted callback decomposition.
In particular the returned head loop and N8 output determine the same body
that appears in the final decoded addition. -/
theorem installed_callback_head_tail_product_value
    (base : Ops) (a : Array Std.U8 608#usize)
    (g : Array Wide 29#usize) (slot : Usize) (value : Wide) (closure' : Closure)
    (hcoords : ∀ j : Fin 29, CoordBound
      (g.val[j.val]'(by simpa [g.property] using j.isLt)))
    (hcall : Callback (install base) (a,g) slot = .ok (value,closure')) :
    ∃ iter limbs body vals wide28 q tailStart tail2 tailValue cs,
      core.iter.traits.iterator.Iterator.step_by.trait_default
        (core.iter.traits.iterator.IteratorRange core.iter.range.StepUsize)
        {start:=0#usize, «end»:=26#usize} 4#usize = .ok iter ∧
      BaseLoop (install base) iter a g slot (Array.repeat 8#usize 0#u64) = .ok limbs ∧
      (install base).arrayFromFn 8#usize
        (AspisR1FastDotsCurrent.fast_dots.four_dots.closure.closure.Insts.CoreOpsFunctionFnMutTupleUsizeU32 (install base))
        limbs = .ok vals ∧
      Array.index_usize g 28#usize=.ok wide28 ∧
      (install base).wideFromLimbs vals=.ok (some body) ∧
      (install base).ebyKNew=.ok EbyKNewToPushStateABI.pushZero ∧
      (install base).ebyKPush EbyKNewToPushStateABI.pushZero wide28 q=.ok (.Ok (),tailStart) ∧
      AspisR1FastDotsActualTailLoopTraceRootV1.RunTrace
        (install base) a g slot {start:=0#usize,«end»:=2#usize}
        tailStart tail2 cs ∧
      (install base).ebyKFinish tail2=.ok tailValue ∧
      (install base).wideAdd body tailValue=.ok value ∧
      cs.map (fun c=>c.term.val)=[0,1] ∧ cs.length=2 ∧
      AspisR1DotCountBoundV1.AcceptedPushTrace
        AspisR1FastDotsPushProductTraceRootV1.raw
        EbyKNewToPushStateABI.pushZero
        ((wide28,q)::cs.map (fun c=>(c.coefficient,c.scalar))) tail2 ∧
      AspisR1FastDotsPushProductTraceRootV1.stateValue tail2=
        ((wide28,q)::cs.map (fun c=>(c.coefficient,c.scalar))).foldl
          AspisR1FastDotsPushProductTraceRootV1.addProduct
          (AspisR1FastDotsPushProductTraceRootV1.stateValue EbyKNewToPushStateABI.pushZero) ∧
      AspisR1CurrentWide.Proof.CanonicalWide (s4ToCurrentE value) ∧
      AspisR1CurrentWide.Proof.decodeWide (s4ToCurrentE value)=
        AspisR1CurrentWide.Proof.decodeWide (s4ToCurrentE body)+
        AspisR1CurrentWide.Proof.decodeWide (s4ToCurrentE tailValue) ∧
      (currentFinishWords tailValue).map (fun w=>w.val)=
        ((tail2.c0.sums.val++tail2.c1.sums.val).map
          (fun x=>x.val % AspisV8R17.RawReducer.P)) := by
  obtain ⟨iter,limbs,body,vals,wide28,q,tailStart,tail2,tailValue,cs,
      hstep,hbase,hvals,hread,hbodySome,hnew,hpush,htrace,hloop,hfinish,hadd,
      hindices,hlen,haccepted,hproduct⟩ :=
    actual_callback_head_tail_product_trace (install base) a g slot value closure'
      hcoords (fun _ _ _ => rfl) rfl hcall
  have hbodycan := AspisR1FastDotsFromLimbsSuccessCanonicalRootV1.installed_from_limbs_success_canonical base _ body hbodySome
  obtain ⟨finished,hfinRun,finish,hmap,hfinCan,hwords⟩ :=
    finishTailCurrent_total tail2
  have hsourceFinish : finishTailCurrent tail2=.ok tailValue := by
    change finishTailCurrent tail2=.ok tailValue
    change finishTailCurrent tail2=.ok _ at hfinish
    exact hfinish
  have hfinEq : finished=tailValue := Result.ok.inj (hfinRun.symm.trans hsourceFinish)
  have htailcan : AspisR1CurrentWide.Proof.CanonicalWide (s4ToCurrentE tailValue) := by
    change AspisR1CurrentWide.Proof.CanonicalWide
      (AspisR1CurrentWide.Proof.ofFinishE finish) at hfinCan
    rw [← hfinEq, ← hmap, finish_carrier_eq]
    exact hfinCan
  have hadd' : currentWideAddS4 body tailValue=.ok value := by
    change currentWideAddS4 body tailValue=.ok value at hadd
    exact hadd
  obtain ⟨sum,haddRun,hsumCan,hsum⟩ :=
    currentWideAddS4_total_exact body tailValue hbodycan htailcan
  have haddValue : currentWideAddS4 body tailValue=.ok value := hadd'
  have hsumEq : sum=value := Result.ok.inj (haddRun.symm.trans haddValue)
  have hfinalCan : AspisR1CurrentWide.Proof.CanonicalWide (s4ToCurrentE value) := by
    simpa only [hsumEq] using hsumCan
  have hfinalValue : AspisR1CurrentWide.Proof.decodeWide (s4ToCurrentE value)=
      AspisR1CurrentWide.Proof.decodeWide (s4ToCurrentE body)+
      AspisR1CurrentWide.Proof.decodeWide (s4ToCurrentE tailValue) := by
    simpa only [hsumEq] using hsum
  obtain ⟨resOut,hresRun,hresValues⟩ := finishTailCurrent_total_residue_values tail2
  have hresOut : resOut=tailValue := Result.ok.inj (hresRun.symm.trans hsourceFinish)
  have hresValues' : (currentFinishWords tailValue).map (fun w=>w.val)=
      ((tail2.c0.sums.val++tail2.c1.sums.val).map
        (fun x=>x.val % AspisV8R17.RawReducer.P)) := by
    simpa only [← hresOut] using hresValues
  exact ⟨iter,limbs,body,vals,wide28,q,tailStart,tail2,tailValue,cs,hstep,hbase,hvals,hread,hbodySome,hnew,
    hpush,htrace,hfinish,hadd,hindices,hlen,haccepted,hproduct,hfinalCan,
    hfinalValue,hresValues'⟩

#print axioms installed_callback_head_tail_product_value
end AspisR1FastDotsHeadTailSharedWitnessRootV1
