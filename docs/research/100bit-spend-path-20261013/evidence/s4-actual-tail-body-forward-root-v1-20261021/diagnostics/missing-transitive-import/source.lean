import S4FirstTailReadTotalRootV1
import FourDotsActualTailParserRootV1
import S4ConcreteTailInstallRootV1
import EbyKPushTotalityV1
set_option autoImplicit false
open Aeneas Aeneas.Std Result
namespace AspisR1FastDotsActualTailBodyForwardRootV1
open AspisR1FastDotsActualCallbackTailTraceRootV1
open AspisR1FastDotsActualTailBodyTraceRootV1 (Range TailBody)
open AspisR1FastDotsTailReadTotalRootV1 (ReadWitness)

theorem installed_parser_scalar_valid
    (base : Ops) (bytes : Slice Std.U8) (q : QM) (hlen : bytes.val.length=16)
    (hparse : (AspisR1FastDotsConcreteTailInstallRootV1.install base).qm31FromBytes bytes = .ok (some q)) :
    ∀ x ∈ (AspisR1EbyKPushDotBackend.scalarQ q).val, x.val < 2147483647 := by
  obtain ⟨limbs,hd,hq,hencode,h0,h1,h2,h3⟩ :=
    AspisR1FastDotsActualTailParserRootV1.parser_slice_success
      (AspisR1FastDotsConcreteTailInstallRootV1.install base) bytes q (some q)
      hlen rfl hparse rfl
  intro x hx
  simp only [AspisR1EbyKPushDotBackend.scalarQ,Array.make,List.mem_cons,
    List.not_mem_nil,or_false] at hx
  rcases hx with hx | hx | hx | hx
  · subst x; exact h0
  · subst x; exact h1
  · subst x; exact h2
  · subst x; exact h3

/-- Actual parser acceptance and the source coefficient read supply the
canonical inputs for the actual emitted push. Push success is a conclusion. -/
theorem installed_push_from_reads
    (base : Ops) (a : Array Std.U8 608#usize) (g : Array Wide 29#usize)
    (slot term : Usize) (r : ReadWitness a g slot term) (q : QM) (old : Tail)
    (hcoords : ∀ j : Fin 29, AspisR1FastDotsTailCoefficientCanonicalV1.CoordBound
      (g.val[j.val]'(by simpa [g.property] using j.isLt)))
    (hcount : old.count < AspisR1EbyKPushExplicitOpsV1.maxTerms)
    (hparse : (AspisR1FastDotsConcreteTailInstallRootV1.install base).qm31FromBytes r.bytes = .ok (some q)) :
    ∃ next : Tail,
      (AspisR1FastDotsConcreteTailInstallRootV1.install base).ebyKPush old r.coefficient q =
        .ok (.Ok (),next) := by
  have hc := AspisR1FastDotsTailCoefficientCanonicalV1.read_push_canonical
    g r.coeffIndex r.coefficient hcoords r.hread
  have hs := installed_parser_scalar_valid base r.bytes q r.bytes_length hparse
  exact AspisR1S5EbyKPushTotalityV1.push_success_of_valid_scalar old r.coefficient q hc hcount hs

/-- The exact extracted tail body returns an accepted continuation under the
same parser/read witnesses and source invariants, without assuming body or
push success or supplying any offset/index success premises separately. -/
theorem actual_tail_body_forward
    (base : Ops) (a : Array Std.U8 608#usize) (g : Array Wide 29#usize)
    (slot term : Usize) (r : ReadWitness a g slot term) (q : QM)
    (iter iter' : Range) (old : Tail)
    (hcoords : ∀ j : Fin 29, AspisR1FastDotsTailCoefficientCanonicalV1.CoordBound
      (g.val[j.val]'(by simpa [g.property] using j.isLt)))
    (hcount : old.count < AspisR1EbyKPushExplicitOpsV1.maxTerms)
    (hnext : core.iter.range.IteratorRange.next core.iter.range.StepUsize iter = .ok (some term,iter'))
    (hparse : (AspisR1FastDotsConcreteTailInstallRootV1.install base).qm31FromBytes r.bytes = .ok (some q)) :
    ∃ next : Tail,
      (AspisR1FastDotsConcreteTailInstallRootV1.install base).ebyKPush old r.coefficient q =
        .ok (.Ok (),next) ∧
      TailBody (AspisR1FastDotsConcreteTailInstallRootV1.install base) a g slot iter old =
        .ok (.cont (iter',next)) := by
  obtain ⟨next,hpush⟩ := installed_push_from_reads base a g slot term r q old hcoords hcount hparse
  exact ⟨next,hpush,AspisR1FastDotsTailReadTotalRootV1.actual_tail_body_from_reads
    (AspisR1FastDotsConcreteTailInstallRootV1.install base) a g slot term iter iter' old next r q
    hnext hparse hpush⟩

#print axioms installed_parser_scalar_valid
#print axioms installed_push_from_reads
#print axioms actual_tail_body_forward
end AspisR1FastDotsActualTailBodyForwardRootV1
