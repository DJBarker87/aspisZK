import S4TailFinishSourceMapV1
import FourDotsActualCallbackTailTraceRootV1
set_option autoImplicit false
open Aeneas Aeneas.Std Result AspisR1FastDotsCurrent
namespace AspisR1FastDotsCallbackTailFinishBridgeV1
open AspisR1FastDotsTailFinishSourceMapV1
abbrev Ops := AspisR1FastDotsCurrent.FourDotsOps
abbrev Wide := AspisR1FastDotsCurrent.aspis_core.field.wide_exact.WideExact
abbrev Tail := AspisR1FastDotsCurrent.fast_pairing.EbyKDot
abbrev Callback := AspisR1FastDotsActualCallbackTailTraceRootV1.Callback
abbrev TailLoop := AspisR1FastDotsActualCallbackTailTraceRootV1.TailLoop

theorem actual_callback_tail_source_finish_residues
    (ops : Ops) (a : Array U8 608#usize) (g : Array Wide 29#usize) (slot : Usize)
    (value : Wide) (c' : AspisR1FastDotsActualCallbackTailTraceRootV1.Closure)
    (h : Callback (withSourceTailFinish ops) (a,g) slot = .ok (value,c')) :
    c'=(a,g) ∧
    ∃ (body : Wide) (pushed : core.result.Result Unit Unit × Tail)
      (tail2 : Tail) (tailValue : Wide),
      TailLoop (withSourceTailFinish ops)
        {start:=0#usize, «end»:=2#usize} a g slot pushed.2 = .ok tail2 ∧
      (withSourceTailFinish ops).ebyKFinish tail2 = .ok tailValue ∧
      currentFinishWords tailValue =
        ((tail2.c0.sums.val ++ tail2.c1.sums.val).map AspisR1EbyKFinish.Proof.word) ∧
      (withSourceTailFinish ops).wideAdd body tailValue = .ok value := by
  obtain ⟨hc,iter,limbs,vals,optBody,body,tail0,wide28,slotOffset,start,finish,
    bytes,optQ,q,pushed,u,tail2,tailValue,hstep,hbase,hvals,hbody,hunwrap,hnew,
    hread,hmul,hadd104,hadd120,hslice,hparse,hunq,hpush,hunpush,htail,hfinish,hadd⟩ :=
    AspisR1FastDotsActualCallbackTailTraceRootV1.actual_callback_success_base_and_tail
      (withSourceTailFinish ops) a g slot value c' h
  rw [withSourceTailFinish_binding] at hfinish
  obtain ⟨out,hrun,fin,hmap,hcanon,hwords⟩ := finishTailCurrent_total tail2
  have hout : out = tailValue := Result.ok.inj (hrun.symm.trans hfinish)
  have hwords' : currentFinishWords tailValue =
      ((tail2.c0.sums.val ++ tail2.c1.sums.val).map AspisR1EbyKFinish.Proof.word) := by
    simpa only [hout] using hwords
  exact ⟨hc,body,pushed,tail2,tailValue,htail,hfinish,hwords',hadd⟩

#print axioms actual_callback_tail_source_finish_residues
end AspisR1FastDotsCallbackTailFinishBridgeV1
