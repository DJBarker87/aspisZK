import S9CandidateTermStagesComposeV1

set_option autoImplicit false
open Aeneas Aeneas.Std Result

namespace AspisR1S9CandidateTermSumsFlatBindV2

open AspisR1S9CandidateTermStagesComposeV1

abbrev C := AspisR1S9CandidateTermStagesV1.C
abbrev P := AspisR1S9CandidateTermStagesV1.P
abbrev CA := AspisR1S9CandidateTermStagesV1.CA
abbrev PA := AspisR1S9CandidateTermStagesV1.PA

/-- Running the staged candidate four-index/three-add prefix and then an arbitrary
continuation equals the flat source-order sequence by Result.bind associativity.
All field operations and Result branches are preserved. -/
private theorem result_bind_assoc {α β γ : Type} (m : Result α)
    (f : α → Result β) (g : β → Result γ) :
    (do
      let y ← (do
        let x ← m
        f x)
      g y) =
    (do
      let x ← m
      let y ← f x
      g y) := by
  cases m <;> rfl

theorem candidateFourTermSums_bind {β : Type} (terms : CA)
    (k : C × C × C → Result β) :
    (do
      let sums ← candidateFourTermSums terms
      k sums) =
    (do
      let x0 ← Array.index_usize terms 0#usize
      let x1 ← Array.index_usize terms 1#usize
      let first2 ← AspisR1S9CandidateHelperV1.field.WideExact.add x0 x1
      let x2 ← Array.index_usize terms 2#usize
      let first3 ← AspisR1S9CandidateHelperV1.field.WideExact.add first2 x2
      let x3 ← Array.index_usize terms 3#usize
      let all ← AspisR1S9CandidateHelperV1.field.WideExact.add first3 x3
      k (first2, first3, all)) := by
  simp only [candidateFourTermSums, cSuffix1, cSuffix2, cSuffix3, cSuffix4, cSuffix5, cSuffix6, AspisR1S9CandidateTermStagesV1.c0, AspisR1S9CandidateTermStagesV1.c1, AspisR1S9CandidateTermStagesV1.c2, AspisR1S9CandidateTermStagesV1.c3, AspisR1S9CandidateTermStagesV1.c4, AspisR1S9CandidateTermStagesV1.c5, AspisR1S9CandidateTermStagesV1.c6, result_bind_assoc, bind_tc_ok]

/-- P6 counterpart of `candidateFourTermSums_bind`, with the same concrete
installed wide-add operation at each of the three source-ordered additions. -/
theorem p6FourTermSums_bind {β : Type} (terms : PA)
    (k : P × P × P → Result β) :
    (do
      let sums ← p6FourTermSums terms
      k sums) =
    (do
      let x0 ← Array.index_usize terms 0#usize
      let x1 ← Array.index_usize terms 1#usize
      let first2 ← @AspisR1S9HelperP6.FieldOps.wideAdd
        AspisR1S9ConcreteFieldOpsV1.concreteFieldOps x0 x1
      let x2 ← Array.index_usize terms 2#usize
      let first3 ← @AspisR1S9HelperP6.FieldOps.wideAdd
        AspisR1S9ConcreteFieldOpsV1.concreteFieldOps first2 x2
      let x3 ← Array.index_usize terms 3#usize
      let all ← @AspisR1S9HelperP6.FieldOps.wideAdd
        AspisR1S9ConcreteFieldOpsV1.concreteFieldOps first3 x3
      k (first2, first3, all)) := by
  simp only [p6FourTermSums, pSuffix1, pSuffix2, pSuffix3, pSuffix4, pSuffix5, pSuffix6, AspisR1S9CandidateTermStagesV1.p0, AspisR1S9CandidateTermStagesV1.p1, AspisR1S9CandidateTermStagesV1.p2, AspisR1S9CandidateTermStagesV1.p3, AspisR1S9CandidateTermStagesV1.p4, AspisR1S9CandidateTermStagesV1.p5, AspisR1S9CandidateTermStagesV1.p6, result_bind_assoc, bind_tc_ok]

#print axioms result_bind_assoc
#print axioms candidateFourTermSums_bind
#print axioms p6FourTermSums_bind

end AspisR1S9CandidateTermSumsFlatBindV2
