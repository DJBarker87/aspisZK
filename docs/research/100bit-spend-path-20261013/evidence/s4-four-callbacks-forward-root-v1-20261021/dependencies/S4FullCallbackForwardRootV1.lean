import S4HeadCoreForwardRootV1
import S4FullTailForwardRootV1
import S4FromLimbsSuccessCanonicalRootV1
set_option autoImplicit false
open Aeneas Aeneas.Std Result
namespace AspisR1FastDotsFullCallbackForwardRootV1
open AspisR1FastDotsHeadLimbForwardRootV1 (Ops)
open AspisR1FastDotsHeadReadForwardRootV1 (Wide)
open AspisR1FastDotsHeadBatchTermsForwardRootV1 (ParsedAt)
open AspisR1FastDotsFirstTailReadTotalRootV1 (FirstReadWitness)
open AspisR1FastDotsTailReadTotalRootV1 (ReadWitness)
abbrev QM := AspisR1FastDotsActualCallbackTailTraceRootV1.QM
abbrev Callback := AspisR1FastDotsCurrent.fast_dots.four_dots.closure.Insts.CoreOpsFunctionFnMutTupleUsizeWideExact.call_mut
abbrev HeadCore := AspisR1FastDotsHeadChainUniqueRootV1.HeadCore
abbrev InstallTail := AspisR1FastDotsConcreteTailInstallRootV1.install
def install (base : Ops) : Ops := AspisR1FastDotsHeadCoreForwardRootV1.headOps (InstallTail base)

theorem tail_install_fixed (base : Ops) : InstallTail (install base)=install base := rfl

theorem finished_tail_canonical (s : AspisR1FastDotsCurrent.fast_pairing.EbyKDot) (out : Wide)
    (hr : AspisR1FastDotsTailFinishSourceMapV1.finishTailCurrent s=.ok out) :
    AspisR1CurrentWide.Proof.CanonicalWide (AspisR1FastDotsTailWideAddCurrentV1.s4ToCurrentE out) := by
  obtain ⟨out',hr',finish,hm,hc,_⟩ := AspisR1FastDotsTailFinishSourceMapV1.finishTailCurrent_total s
  have heq : out'=out := Result.ok.inj (hr'.symm.trans hr)
  rw [← heq,← hm]
  exact hc

theorem full_callback_forward
    (base : Ops) (a : Array Std.U8 608#usize) (g : Array Wide 29#usize) (slot : Usize)
    (hcoords : ∀ j : Fin 29, AspisR1FastDotsWideLimbCanonical.CoordinateBound
      (g.val[j.val]'(by simpa [g.property] using j.isLt)))
    (hparsed : ∀ term : Usize, term.val<26 → ParsedAt a g slot term)
    (first : FirstReadWitness a g slot)
    (r0 : ReadWitness a g slot 0#usize) (r1 : ReadWitness a g slot 1#usize)
    (qfirst q0 q1 : QM)
    (hpf : (install base).qm31FromBytes first.bytes=.ok (some qfirst))
    (hp0 : (install base).qm31FromBytes r0.bytes=.ok (some q0))
    (hp1 : (install base).qm31FromBytes r1.bytes=.ok (some q1)) :
    ∃ out : Wide, Callback (install base) (a,g) slot=.ok (out,(a,g)) ∧
      AspisR1CurrentWide.Proof.CanonicalWide (AspisR1FastDotsTailWideAddCurrentV1.s4ToCurrentE out) := by
  obtain ⟨limbs,values,body,hhead,_hbound,_hwords⟩ :=
    AspisR1FastDotsHeadCoreForwardRootV1.head_core_forward (InstallTail base) a g slot hcoords hparsed
  change HeadCore (install base) a g slot _ limbs values body at hhead
  rcases hhead with ⟨hi,hl,ha,hpack⟩
  have hcoordsTail : ∀ j : Fin 29, AspisR1FastDotsHeadTailSharedWitnessRootV2.CoordBound
      (g.val[j.val]'(by simpa [g.property] using j.isLt)) := hcoords
  have hpf' : (InstallTail (install base)).qm31FromBytes first.bytes=.ok (some qfirst) := by
    simpa only [tail_install_fixed] using hpf
  have hp0' : (InstallTail (install base)).qm31FromBytes r0.bytes=.ok (some q0) := by
    simpa only [tail_install_fixed] using hp0
  have hp1' : (InstallTail (install base)).qm31FromBytes r1.bytes=.ok (some q1) := by
    simpa only [tail_install_fixed] using hp1
  obtain ⟨tailStart,tail2,tailValue,cs,hnew,_hfirst,hpush,htail,_hinv,_hc,_ht,_hindices,_hlen,hfinish,_hsum⟩ :=
    AspisR1FastDotsFullTailForwardRootV1.full_tail_forward_field_sum
      (install base) a g slot first r0 r1 qfirst q0 q1 hcoordsTail hpf' hp0' hp1'
  have hfixed : AspisR1FastDotsTailLoopForwardRootV1.Install (install base)=install base := rfl
  rw [hfixed] at hnew hpush htail hfinish
  have hbodyCan := AspisR1FastDotsFromLimbsSuccessCanonicalRootV1.installed_from_limbs_success_canonical
    (install base) values body (by simpa only [tail_install_fixed] using hpack)
  have htailCan := finished_tail_canonical tail2 tailValue hfinish
  obtain ⟨out,hadd,hcan,_hdecode⟩ := AspisR1FastDotsTailWideAddCurrentV1.currentWideAddS4_total_exact
    body tailValue hbodyCan htailCan
  have hadd' : (install base).wideAdd body tailValue=.ok out := hadd
  have hslice := first.hslice
  rw [Array.index_SliceIndexRangeUsizeSlice] at hslice
  refine ⟨out,?_,hcan⟩
  simp [Callback,
    AspisR1FastDotsCurrent.fast_dots.four_dots.closure.Insts.CoreOpsFunctionFnMutTupleUsizeWideExact.call_mut,
    hi,hl,ha,hpack,core.option.Option.unwrap,Result.ofOption,bind_tc_ok,
    hnew,first.hcoefficient,first.hmul,first.hstart,first.hfinish,hslice,hpf,
    hpush,core.result.Result.unwrap,htail,hfinish,hadd']

#print axioms tail_install_fixed
#print axioms finished_tail_canonical
#print axioms full_callback_forward
end AspisR1FastDotsFullCallbackForwardRootV1
