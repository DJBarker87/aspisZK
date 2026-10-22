import S4TailRangeNextRootV1
import EbyKPushStateInvariantStepV1
set_option autoImplicit false
open Aeneas Aeneas.Std Result
namespace AspisR1FastDotsTailLoopForwardRootV1
open AspisR1FastDotsActualCallbackTailTraceRootV1
open AspisR1FastDotsActualTailBodyTraceRootV1 (Range TailBody Contribution)
open AspisR1FastDotsTailReadTotalRootV1 (ReadWitness)
open AspisR1FastDotsActualTailBodyForwardRootV1
abbrev Install := AspisR1FastDotsConcreteTailInstallRootV1.install
abbrev CoordBound := AspisR1FastDotsTailCoefficientCanonicalV1.CoordBound

def CountInvariant (s : Tail) : Prop :=
  AspisR1FinishDotCountBoundV2.sumsBelowCount s.count.val s.c0.sums ∧
  AspisR1FinishDotCountBoundV2.sumsBelowCount s.count.val s.c1.sums

/-- The actual body preserves the count invariant in the same returned state;
all backend successes come from canonical source reads and parser acceptance. -/
theorem tail_body_state_step
    (base : Ops) (a : Array Std.U8 608#usize) (g : Array Wide 29#usize)
    (slot term : Usize) (r : ReadWitness a g slot term) (q : QM)
    (iter iter' : Range) (old : Tail)
    (hcoords : ∀ j : Fin 29, CoordBound (g.val[j.val]'(by simpa [g.property] using j.isLt)))
    (hguard : old.count < AspisR1EbyKPushExplicitOpsV1.maxTerms)
    (hinv : CountInvariant old)
    (hnext : core.iter.range.IteratorRange.next core.iter.range.StepUsize iter = .ok (some term,iter'))
    (hparse : (Install base).qm31FromBytes r.bytes = .ok (some q)) :
    ∃ out : Tail,
      TailBody (Install base) a g slot iter old = .ok (.cont (iter',out)) ∧
      CountInvariant out ∧ out.count.val=old.count.val+1 := by
  have hc := AspisR1FastDotsTailCoefficientCanonicalV1.read_push_canonical
    g r.coeffIndex r.coefficient hcoords r.hread
  have hs := installed_parser_scalar_valid base r.bytes q r.bytes_length hparse
  obtain ⟨out,hpush,hinv0,hinv1,hinc,_prod0,_prod1⟩ :=
    AspisR1S5EbyKPushStateInvariantStepV1.push_success_state_step old r.coefficient q
      hc hguard hs hinv.1 hinv.2
  have hb := AspisR1FastDotsTailReadTotalRootV1.actual_tail_body_from_reads
    (Install base) a g slot term iter iter' old out r q hnext hparse hpush
  exact ⟨out,hb,⟨hinv0,hinv1⟩,hinc⟩

/-- Two source tail iterations execute from the actual count-one state left
by the first push. This constructs the full loop success and its exact two
source contributions; neither loop nor push success is assumed. -/
theorem actual_two_term_tail_forward
    (base : Ops) (a : Array Std.U8 608#usize) (g : Array Wide 29#usize) (slot : Usize)
    (r0 : ReadWitness a g slot 0#usize) (r1 : ReadWitness a g slot 1#usize)
    (q0 q1 : QM) (old : Tail)
    (hcoords : ∀ j : Fin 29, CoordBound (g.val[j.val]'(by simpa [g.property] using j.isLt)))
    (hcount : old.count.val=1) (hinv : CountInvariant old)
    (hp0 : (Install base).qm31FromBytes r0.bytes = .ok (some q0))
    (hp1 : (Install base).qm31FromBytes r1.bytes = .ok (some q1)) :
    ∃ out : Tail, ∃ cs : List Contribution,
      TailLoop (Install base) {start:=0#usize,«end»:=2#usize} a g slot old = .ok out ∧
      CountInvariant out ∧ out.count.val=3 ∧
      AspisR1FastDotsActualTailLoopTraceRootV1.RunTrace (Install base) a g slot
        {start:=0#usize,«end»:=2#usize} old out cs ∧
      cs.map (fun c=>c.term.val)=[0,1] ∧ cs.length=2 := by
  let rStart : Range := {start:=0#usize,«end»:=2#usize}
  let rMid : Range := {start:=1#usize,«end»:=2#usize}
  let rDone : Range := {start:=2#usize,«end»:=2#usize}
  have hn0 : core.iter.range.IteratorRange.next core.iter.range.StepUsize rStart =
      .ok (some 0#usize,rMid) :=
    AspisR1FastDotsTailRangeNextRootV1.range_next_succ 0#usize 2#usize 1#usize (by decide) (by decide)
  have hn1 : core.iter.range.IteratorRange.next core.iter.range.StepUsize rMid =
      .ok (some 1#usize,rDone) :=
    AspisR1FastDotsTailRangeNextRootV1.range_next_succ 1#usize 2#usize 2#usize (by decide) (by decide)
  have hg0 : old.count < AspisR1EbyKPushExplicitOpsV1.maxTerms := by
    change old.count.val < AspisR1EbyKPushExplicitOpsV1.maxTerms.val
    rw [hcount]
    norm_num [AspisR1EbyKPushExplicitOpsV1.maxTerms]
  obtain ⟨mid,hb0,hinvMid,hinc0⟩ := tail_body_state_step base a g slot 0#usize r0 q0
    rStart rMid old hcoords hg0 hinv hn0 hp0
  have hmidCount : mid.count.val=2 := by omega
  have hg1 : mid.count < AspisR1EbyKPushExplicitOpsV1.maxTerms := by
    change mid.count.val < AspisR1EbyKPushExplicitOpsV1.maxTerms.val
    rw [hmidCount]
    norm_num [AspisR1EbyKPushExplicitOpsV1.maxTerms]
  obtain ⟨out,hb1,hinvOut,hinc1⟩ := tail_body_state_step base a g slot 1#usize r1 q1
    rMid rDone mid hcoords hg1 hinvMid hn1 hp1
  have hdone : TailBody (Install base) a g slot rDone out = .ok (.done out) :=
    AspisR1FastDotsTailRangeNextRootV1.actual_tail_body_done (Install base) a g slot 2#usize out
  let step : (Range × Tail) → Result (ControlFlow (Range × Tail) Tail) :=
    fun st => TailBody (Install base) a g slot st.1 st.2
  have hloop : TailLoop (Install base) rStart a g slot old = .ok out := by
    change Aeneas.Std.loop step (rStart,old) = .ok out
    rw [Aeneas.Std.loop.eq_def]
    simp only [step,hb0,bind_tc_ok]
    rw [Aeneas.Std.loop.eq_def]
    simp only [step,hb1,bind_tc_ok]
    rw [Aeneas.Std.loop.eq_def]
    simp only [step,hdone,bind_tc_ok]
  obtain ⟨cs,htrace,hindices,hlen⟩ :=
    AspisR1FastDotsActualTailLoopTraceRootV1.actual_two_term_tail_success_trace
      (Install base) a g slot old out hloop
  exact ⟨out,cs,hloop,hinvOut,by omega,htrace,hindices,hlen⟩

#print axioms tail_body_state_step
#print axioms actual_two_term_tail_forward
end AspisR1FastDotsTailLoopForwardRootV1
