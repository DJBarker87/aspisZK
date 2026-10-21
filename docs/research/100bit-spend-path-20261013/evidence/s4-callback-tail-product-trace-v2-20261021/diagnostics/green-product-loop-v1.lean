import FourDotsActualTailInputMeaningRootV1
import FourDotsTailAcceptedTraceRootV1
import FourDotsPushProductTraceRootV1
import EbyKPowerValueCanonicalToPushV5
import S4TailCoefficientCanonicalV1
set_option autoImplicit false
open Aeneas Aeneas.Std Result
namespace AspisR1FastDotsCallbackTailProductTraceV1
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
theorem actual_callback_tail_product_trace
    (ops : Ops) (a : Array Std.U8 608#usize)
    (g : Array Wide 29#usize) (slot : Usize) (value : Wide) (closure' : Closure)
    (hcoords : ∀ j : Fin 29, CoordBound
      (g.val[j.val]'(by simpa [g.property] using j.isLt)))
    (hpushbinding : PushBinding ops AspisR1FastDotsPushProductTraceRootV1.raw)
    (hnewbinding : ops.ebyKNew=AspisR1FastDotsTailAcceptedTraceRootV1.newFromSource)
    (hcall : Callback ops (a,g) slot=.ok (value,closure')) :
    ∃ wide28 q tailStart tail2 cs,
      Array.index_usize g 28#usize=.ok wide28 ∧
      ops.ebyKNew=.ok EbyKNewToPushStateABI.pushZero ∧
      ops.ebyKPush EbyKNewToPushStateABI.pushZero wide28 q=
        .ok (.Ok (),tailStart) ∧
      RunTrace ops a g slot {start:=0#usize, «end»:=2#usize}
        tailStart tail2 cs ∧
      AspisR1FastDotsActualCallbackTailTraceRootV1.TailLoop ops
        {start:=0#usize, «end»:=2#usize} a g slot tailStart = .ok tail2 ∧
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
  have hnewzero : ops.ebyKNew=.ok EbyKNewToPushStateABI.pushZero := by
    rw [hnewbinding,AspisR1FastDotsTailAcceptedTraceRootV1.newFromSource_zero]
  exact ⟨wide28,q,pushed.2,tail2,cs,hread,hnewzero,hsourcepush,htrace,
    _hindices,hloop,_hlen,hfull,hproduct⟩

#print axioms actual_callback_tail_product_trace
end AspisR1FastDotsCallbackTailProductTraceV1
