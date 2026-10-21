import S4CallbackTailProductTraceV1
import S4TailFinishSourceMapV1
import S4TailWideAddCurrentV1
set_option autoImplicit false
open Aeneas Aeneas.Std Result AspisR1FastDotsCurrent
namespace AspisR1FastDotsCallbackTailFinishProductV1
open AspisR1FastDotsCallbackTailProductTraceV1
open AspisR1FastDotsTailFinishSourceMapV1
open AspisR1FastDotsTailWideAddCurrentV1

abbrev Ops := AspisR1FastDotsCurrent.FourDotsOps
abbrev Wide := AspisR1FastDotsCurrent.aspis_core.field.wide_exact.WideExact
abbrev Closure := AspisR1FastDotsActualCallbackTailTraceRootV1.Closure
abbrev Callback := AspisR1FastDotsActualCallbackTailTraceRootV1.Callback

def withTailFinishAdd (ops : Ops) : Ops :=
  withSourceTailFinish (withCurrentWideAdd ops)

theorem finish_carrier_eq (f : AspisR1CurrentWide.Proof.FinishE) :
    s4ToCurrentE (finishEToCurrent f) = AspisR1CurrentWide.Proof.ofFinishE f := by
  cases f
  rfl

theorem actual_callback_finish_product_value
    (ops : Ops) (a : Array Std.U8 608#usize)
    (g : Array Wide 29#usize) (slot : Usize) (value : Wide) (closure' : Closure)
    (hcoords : ∀ j : Fin 29, CoordBound
      (g.val[j.val]'(by simpa [g.property] using j.isLt)))
    (hpushbinding : AspisR1FastDotsTailAcceptedTraceRootV1.PushBinding
      ops AspisR1FastDotsPushProductTraceRootV1.raw)
    (hnewbinding : ops.ebyKNew=AspisR1FastDotsTailAcceptedTraceRootV1.newFromSource)
    (hbodyCanonical : ∀ vals body,
      ops.wideFromLimbs vals = .ok (some body) →
      AspisR1CurrentWide.Proof.CanonicalWide (s4ToCurrentE body))
    (hcall : Callback (withTailFinishAdd ops) (a,g) slot=.ok (value,closure')) :
    ∃ body vals wide28 q tailStart tail2 tailValue cs,
      Array.index_usize g 28#usize=.ok wide28 ∧
      ops.wideFromLimbs vals=.ok (some body) ∧
      (withTailFinishAdd ops).ebyKNew=.ok EbyKNewToPushStateABI.pushZero ∧
      ops.ebyKPush EbyKNewToPushStateABI.pushZero wide28 q=.ok (.Ok (),tailStart) ∧
      AspisR1FastDotsActualTailLoopTraceRootV1.RunTrace
        (withTailFinishAdd ops) a g slot {start:=0#usize,«end»:=2#usize}
        tailStart tail2 cs ∧
      (withTailFinishAdd ops).ebyKFinish tail2=.ok tailValue ∧
      (withTailFinishAdd ops).wideAdd body tailValue=.ok value ∧
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
  have hpush' : AspisR1FastDotsTailAcceptedTraceRootV1.PushBinding
      (withTailFinishAdd ops) AspisR1FastDotsPushProductTraceRootV1.raw := by
    intro s v q
    exact hpushbinding s v q
  have hnew' : (withTailFinishAdd ops).ebyKNew=
      AspisR1FastDotsTailAcceptedTraceRootV1.newFromSource := hnewbinding
  obtain ⟨body,vals,wide28,q,tailStart,tail2,tailValue,cs,hread,hbodySome,hnew,hpush,
      htrace,hloop,hfinish,hadd,hindices,hlen,haccepted,hproduct⟩ :=
    AspisR1FastDotsCallbackTailProductTraceV1.actual_callback_tail_product_trace
      (withTailFinishAdd ops) a g slot value closure' hcoords hpush' hnew' hcall
  have hbodycan := hbodyCanonical _ body hbodySome
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
  exact ⟨body,vals,wide28,q,tailStart,tail2,tailValue,cs,hread,hbodySome,hnew,
    hpush,htrace,hfinish,hadd,hindices,hlen,haccepted,hproduct,hfinalCan,
    hfinalValue,hresValues'⟩

#print axioms actual_callback_finish_product_value
end AspisR1FastDotsCallbackTailFinishProductV1
