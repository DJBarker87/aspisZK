import S4TailLoopForwardRootV1
import S4TailLiteralProductsRootV1
set_option autoImplicit false
open Aeneas Aeneas.Std Result
namespace AspisR1FastDotsFullTailForwardRootV1
open AspisR1FastDotsActualCallbackTailTraceRootV1
open AspisR1FastDotsActualTailBodyTraceRootV1 (Contribution)
open AspisR1FastDotsTailLoopForwardRootV1
open AspisR1FastDotsFirstTailReadTotalRootV1 (FirstReadWitness)
open AspisR1FastDotsTailReadTotalRootV1 (ReadWitness)
abbrev zero := EbyKNewToPushStateABI.pushZero
abbrev raw := AspisR1FastDotsPushProductTraceRootV1.raw

theorem source_zero_count_invariant : CountInvariant zero := by
  constructor <;> intro j hj <;>
    change ((List.replicate 4 (0#u64))[j]'hj).val ≤ 0*2^34
  all_goals
    rw [List.getElem_replicate]
    exact Nat.le_refl 0

/-- The source constructor and the parsed first scalar produce the actual
count-one state. No push success or accumulator range is assumed. -/
theorem first_push_forward
    (base : Ops) (a : Array Std.U8 608#usize) (g : Array Wide 29#usize)
    (slot : Usize) (r : FirstReadWitness a g slot) (q : QM)
    (hcoords : ∀ j : Fin 29, CoordBound (g.val[j.val]'(by simpa [g.property] using j.isLt)))
    (hparse : (Install base).qm31FromBytes r.bytes = .ok (some q)) :
    ∃ out : Tail,
      (Install base).ebyKNew = .ok zero ∧
      (Install base).ebyKPush zero r.coefficient q = .ok (.Ok (),out) ∧
      CountInvariant out ∧ out.count.val=1 := by
  have hc := AspisR1FastDotsTailCoefficientCanonicalV1.read_push_canonical
    g 28#usize r.coefficient hcoords r.hcoefficient
  have hs := AspisR1FastDotsActualTailBodyForwardRootV1.installed_parser_scalar_valid
    base r.bytes q r.bytes_length hparse
  have hg : zero.count < AspisR1EbyKPushExplicitOpsV1.maxTerms := by
    change (0#usize : Usize) < AspisR1EbyKPushExplicitOpsV1.maxTerms
    norm_num [AspisR1EbyKPushExplicitOpsV1.maxTerms]
  obtain ⟨out,hpush,h0,h1,hinc,_prod0,_prod1⟩ :=
    AspisR1S5EbyKPushStateInvariantStepV1.push_success_state_step zero r.coefficient q
      hc hg hs source_zero_count_invariant.1 source_zero_count_invariant.2
  refine ⟨out,AspisR1FastDotsConcreteTailInstallRootV1.new_zero base,hpush,⟨h0,h1⟩,?_⟩
  change out.count.val = zero.count.val+1 at hinc
  simpa only [show zero.count.val=0 from rfl] using hinc

/-- Complete tail execution from the actual source constructor through three
pushes and finish, with the decoded result equal to the same ordered source
products. Parser acceptance and scratch provenance remain caller obligations;
no child push, loop or finish success is assumed. -/
theorem full_tail_forward_field_sum
    (base : Ops) (a : Array Std.U8 608#usize) (g : Array Wide 29#usize) (slot : Usize)
    (first : FirstReadWitness a g slot)
    (r0 : ReadWitness a g slot 0#usize) (r1 : ReadWitness a g slot 1#usize)
    (qfirst q0 q1 : QM)
    (hcoords : ∀ j : Fin 29, CoordBound (g.val[j.val]'(by simpa [g.property] using j.isLt)))
    (hpf : (Install base).qm31FromBytes first.bytes = .ok (some qfirst))
    (hp0 : (Install base).qm31FromBytes r0.bytes = .ok (some q0))
    (hp1 : (Install base).qm31FromBytes r1.bytes = .ok (some q1)) :
    ∃ tailStart tail2 : Tail, ∃ tailValue : Wide, ∃ cs : List Contribution,
      (Install base).ebyKNew = .ok zero ∧
      AspisR1FastDotsHeadTailSharedWitnessRootV2.FirstQueryInput (Install base) a slot qfirst ∧
      (Install base).ebyKPush zero first.coefficient qfirst = .ok (.Ok (),tailStart) ∧
      TailLoop (Install base) {start:=0#usize,«end»:=2#usize} a g slot tailStart = .ok tail2 ∧
      CountInvariant tail2 ∧ tail2.count.val=3 ∧
      AspisR1FastDotsActualTailLoopTraceRootV1.RunTrace (Install base) a g slot
        {start:=0#usize,«end»:=2#usize} tailStart tail2 cs ∧
      cs.map (fun c=>c.term.val)=[0,1] ∧ cs.length=2 ∧
      (Install base).ebyKFinish tail2 = .ok tailValue ∧
      AspisR1CurrentWide.Proof.decodeWide
        (AspisR1FastDotsTailWideAddCurrentV1.s4ToCurrentE tailValue) =
        (((first.coefficient,qfirst)::cs.map (fun c=>(c.coefficient,c.scalar))).map
          (fun p=>AspisR1FastDotsTailFieldProductRootV1.wideDecoded p.1 *
            AspisR1FastDotsTailLiteralProductsRootV1.embedQM p.2)).sum := by
  obtain ⟨tailStart,hnew,hfirstPush,hinvStart,hcountStart⟩ :=
    first_push_forward base a g slot first qfirst hcoords hpf
  obtain ⟨tail2,cs,hloop,hinvTail,hcountTail,htrace,hindices,hlen⟩ :=
    actual_two_term_tail_forward base a g slot r0 r1 q0 q1 tailStart hcoords
      hcountStart hinvStart hp0 hp1
  have hbinding : AspisR1FastDotsTailAcceptedTraceRootV1.PushBinding (Install base) raw :=
    fun _ _ _ => rfl
  have htailAccepted := AspisR1FastDotsTailAcceptedTraceRootV1.actual_tail_trace_checked_pushes
    (Install base) raw a g slot _ tailStart tail2 cs hbinding htrace
  have haccepted : AspisR1DotCountBoundV1.AcceptedPushTrace raw zero
      ((first.coefficient,qfirst)::cs.map (fun c=>(c.coefficient,c.scalar))) tail2 :=
    .cons zero tailStart tail2 first.coefficient qfirst _ hfirstPush htailAccepted
  have hfirstCanonical := AspisR1FastDotsTailCoefficientCanonicalV1.read_push_canonical
    g 28#usize first.coefficient hcoords first.hcoefficient
  have htailCanonical := AspisR1FastDotsTailCoefficientCanonicalV1.trace_coefficients_canonical
    (Install base) a g slot _ tailStart tail2 cs hcoords htrace
  have hcanonical : ∀ p ∈ ((first.coefficient,qfirst)::cs.map (fun c=>(c.coefficient,c.scalar))),
      AspisR1EbyKPowerValueCanonicalToPush.pushCanonical p.1 := by
    intro p hp
    rcases List.mem_cons.mp hp with hp | hp
    · cases hp
      exact hfirstCanonical
    · obtain ⟨c,hc,heq⟩ := List.mem_map.mp hp
      subst p
      exact htailCanonical c hc
  have hproduct := AspisR1FastDotsPushProductTraceRootV1.accepted_trace_product_sum
    zero tail2 ((first.coefficient,qfirst)::cs.map (fun c=>(c.coefficient,c.scalar)))
    source_zero_count_invariant.1 source_zero_count_invariant.2 hcanonical haccepted
  obtain ⟨tailValue,hfinish,hwords⟩ :=
    AspisR1FastDotsTailFinishSourceMapV1.finishTailCurrent_total_residue_values tail2
  have hdecode := AspisR1FastDotsTailLiteralProductsRootV1.finished_tail_eq_literal_sum
    tail2 tailValue ((first.coefficient,qfirst)::cs.map (fun c=>(c.coefficient,c.scalar))) hproduct hwords
  exact ⟨tailStart,tail2,tailValue,cs,hnew,
    AspisR1FastDotsFirstTailReadTotalRootV1.first_query_input_of_reads
      (Install base) a g slot first qfirst hpf,
    hfirstPush,hloop,hinvTail,hcountTail,htrace,hindices,hlen,hfinish,hdecode⟩

#print axioms source_zero_count_invariant
#print axioms first_push_forward
#print axioms full_tail_forward_field_sum
end AspisR1FastDotsFullTailForwardRootV1
