import S4ConcreteTailInstallRootV1
import EbyKPushDotBackend
import AspisR1EbyKPushConcreteCheckedQV1
import EbyKCheckedQConcreteAll
import AspisR1EbyKPushSourceConversionV1
import AspisR1EbyKPushExplicitOpsV1
import AspisR1EbyKPushWideToQ
import FourDotsTailAcceptedTraceRootV1
import S4TailFinishSourceMapV1
import EbyKNewToPushStateABI
import S5QRaw.EbyKPushDecodedProductUpdateV1
open Aeneas Aeneas.Std Result ControlFlow

namespace AspisR1FastDotsConcreteTailInstalledThreePushesV1

abbrev Ops := AspisR1FastDotsConcreteTailInstallRootV1.Ops
abbrev Wide := AspisR1FastDotsActualCallbackTailTraceRootV1.Wide
abbrev QM := AspisR1FastDotsActualCallbackTailTraceRootV1.QM
abbrev Tail := AspisR1FastDotsActualCallbackTailTraceRootV1.Tail
abbrev Closure := AspisR1FastDotsActualCallbackTailTraceRootV1.Closure
abbrev Callback := AspisR1FastDotsActualCallbackTailTraceRootV1.Callback

/-- A successful callback through the concrete installed operation record
supplies the same three accepted QRaw pushes, exact tail state/count, and the
same installed source finish result. The final finish words are the residues
of that exact tail state; no child operation-success assumptions are passed. -/
theorem installed_callback_three_pushes_and_finish_residues
    (base : Ops) (a : Array U8 608#usize) (g : Array Wide 29#usize)
    (slot : Usize) (value : Wide) (closure' : Closure)
    (hcall : Callback (AspisR1FastDotsConcreteTailInstallRootV1.install base)
      (a,g) slot = .ok (value,closure')) :
    ∃ (wide28 : Wide) (q : QM) (tailOut : Tail) (cs : List AspisR1FastDotsActualTailBodyTraceRootV1.Contribution)
      (body : Wide) (tailValue : Wide),
      Array.index_usize g 28#usize = .ok wide28 ∧
      cs.map (fun c => c.term.val) = [0,1] ∧ cs.length = 2 ∧
      AspisR1DotCountBoundV1.AcceptedPushTrace
        AspisR1EbyKPushDecodedProductUpdate.QRaw
        EbyKNewToPushStateABI.pushZero
        ((wide28,q)::cs.map (fun c => (c.coefficient,c.scalar))) tailOut ∧
      tailOut.count.val = 3 ∧
      AspisR1FastDotsTailFinishSourceMapV1.finishTailCurrent tailOut = .ok tailValue ∧
      (AspisR1FastDotsTailFinishSourceMapV1.currentFinishWords tailValue).map (fun w => w.val) =
        ((tailOut.c0.sums.val ++ tailOut.c1.sums.val).map
          (fun x => x.val % AspisV8R17.RawReducer.P)) ∧
      (AspisR1FastDotsConcreteTailInstallRootV1.install base).wideAdd body tailValue = .ok value := by
  have hbindings := AspisR1FastDotsConcreteTailInstallRootV1.source_bindings base
  obtain ⟨wide28,q,tailOut,cs,hread,hcs,hlen,htrace,hcount,hbelow0,hbelow1,
    hacc0,hacc1,body,tailValue,hfinish,hadd⟩ :=
    AspisR1FastDotsTailAcceptedTraceRootV1.actual_callback_three_checked_pushes
      (AspisR1FastDotsConcreteTailInstallRootV1.install base)
      AspisR1EbyKPushDecodedProductUpdate.QRaw a g slot value closure'
      hbindings.2.1 hbindings.1 hcall
  have hfinish' : AspisR1FastDotsTailFinishSourceMapV1.finishTailCurrent tailOut = .ok tailValue := by
    rw [← hbindings.2.2.1]
    exact hfinish
  obtain ⟨out,hout,hwords⟩ :=
    AspisR1FastDotsTailFinishSourceMapV1.finishTailCurrent_total_residue_values tailOut
  have houtEq : out = tailValue := Result.ok.inj (hout.symm.trans hfinish')
  refine ⟨wide28,q,tailOut,cs,body,tailValue,hread,hcs,hlen,htrace,hcount,hfinish',?_,hadd⟩
  simpa [houtEq] using hwords

open AspisR1EbyKPushExplicitOpsV1

abbrev ConcreteCheckedQ : Qm → Result (core.result.Result Q Unit) :=
  AspisR1EbyKPushConcreteCheckedQV1.checkedQWithAll
    AspisR1EbyKCheckedQConcreteAll.concreteAll
abbrev ConcreteDotPush : Dot → Q → Q → Result Dot :=
  AspisR1EbyKPushDotBackend.dotViaRaw
    AspisR1EbyKPushDecodedProductUpdate.QRaw

/-- Exact full-result equation to the explicit-argument version of the
emitted `EbyKDot.push` control body. Every failure/error branch is retained. -/
theorem qraw_backend_eq_explicit_source_control
    (self : State) (value : Wide) (scalar : Qm) :
    AspisR1EbyKPushDotBackend.pushWithDotBackend
        AspisR1EbyKPushDecodedProductUpdate.QRaw self value scalar =
      AspisR1EbyKPushExplicitOpsV1.pushWithOps
        AspisR1EbyKPushWideToQ.fromWide ConcreteCheckedQ ConcreteDotPush
        UScalar.add self value scalar := by
  rfl

/-- Same successful callback supplies its ordered 3-push/finish trace while
this conclusion fixes the exact full-result source control semantics of the
installed push slot. -/
theorem installed_callback_three_pushes_and_explicit_push_control
    (base : Ops) (a : Array U8 608#usize) (g : Array Wide 29#usize)
    (slot : Usize) (value : Wide) (closure' : Closure)
    (hcall : Callback (AspisR1FastDotsConcreteTailInstallRootV1.install base)
      (a,g) slot = .ok (value,closure')) :
    (∃ (wide28 : Wide) (q : QM) (tailOut : Tail)
        (cs : List AspisR1FastDotsActualTailBodyTraceRootV1.Contribution)
        (body : Wide) (tailValue : Wide),
      Array.index_usize g 28#usize = .ok wide28 ∧
      cs.map (fun c => c.term.val) = [0,1] ∧ cs.length = 2 ∧
      AspisR1DotCountBoundV1.AcceptedPushTrace
        AspisR1EbyKPushDecodedProductUpdate.QRaw
        EbyKNewToPushStateABI.pushZero
        ((wide28,q)::cs.map (fun c => (c.coefficient,c.scalar))) tailOut ∧
      tailOut.count.val = 3 ∧
      AspisR1FastDotsTailFinishSourceMapV1.finishTailCurrent tailOut = .ok tailValue ∧
      (AspisR1FastDotsTailFinishSourceMapV1.currentFinishWords tailValue).map (fun w => w.val) =
        ((tailOut.c0.sums.val ++ tailOut.c1.sums.val).map
          (fun x => x.val % AspisV8R17.RawReducer.P)) ∧
      (AspisR1FastDotsConcreteTailInstallRootV1.install base).wideAdd body tailValue = .ok value) ∧
    (∀ self value scalar,
      AspisR1EbyKPushDotBackend.pushWithDotBackend
        AspisR1EbyKPushDecodedProductUpdate.QRaw self value scalar =
      AspisR1EbyKPushExplicitOpsV1.pushWithOps
        AspisR1EbyKPushWideToQ.fromWide ConcreteCheckedQ ConcreteDotPush
        UScalar.add self value scalar) := by
  refine ⟨?_, ?_⟩
  · exact installed_callback_three_pushes_and_finish_residues base a g slot value closure' hcall
  · intro self value scalar
    exact qraw_backend_eq_explicit_source_control self value scalar

#print axioms installed_callback_three_pushes_and_finish_residues
#print axioms qraw_backend_eq_explicit_source_control
#print axioms installed_callback_three_pushes_and_explicit_push_control
end AspisR1FastDotsConcreteTailInstalledThreePushesV1
