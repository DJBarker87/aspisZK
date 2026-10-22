import S9CandidateSideZeroTailMapV1
import S9SideZeroTailRootV1
import S9CandidateSideOneTailMapV4

set_option autoImplicit false
open Aeneas Aeneas.Std Result

namespace AspisR1S9CandidateTailFlatBindV1

/-- Generic associativity for the generated Result bind. -/
theorem result_bind_assoc {α β γ : Type} (m : Result α)
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

/-- Candidate side-zero tail followed by an arbitrary continuation, flattened
without changing its field-operation or checked-update order. -/
theorem candidateSideZeroTail_bind {β : Type}
    (old : AspisR1S9CandidateSideZeroTailMapV1.CA)
    (low first3 all : AspisR1S9CandidateSideZeroTailMapV1.C)
    (q16 : AspisR1S9CandidateSideZeroTailMapV1.CQ)
    (k : AspisR1S9CandidateSideZeroTailMapV1.CA → Result β) :
    (do
      let out ← AspisR1S9CandidateSideZeroTailMapV1.candidateSideZeroTail
        old low first3 all q16
      k out) =
    (do
      let we12 ← AspisR1S9CandidateHelperV1.field.WideExact.mul low all
      let weights1 ← Array.update old 0#usize we12
      let we13 ← AspisR1S9CandidateHelperV1.field.WideExact.mul low first3
      let we14 ← AspisR1S9CandidateHelperV1.field.WideExact.mul_qm31 we13 q16
      let out ← Array.update weights1 1#usize we14
      k out) := by
  simp only [AspisR1S9CandidateSideZeroTailMapV1.candidateSideZeroTail,
    result_bind_assoc, bind_tc_ok]

/-- P6 side-zero tail followed by an arbitrary continuation, with the exact
installed wide-operation slots and write order. -/
theorem p6SideZeroTail_bind {β : Type}
    (old : AspisR1.S9SideZeroTailRootV1.A)
    (low first3 all : AspisR1.S9SideZeroTailRootV1.W)
    (q16 : AspisR1.S9SideZeroTailRootV1.Q)
    (k : AspisR1.S9SideZeroTailRootV1.A → Result β) :
    (do
      let out ← AspisR1.S9SideZeroTailRootV1.sideZeroTail
        old low first3 all q16
      k out) =
    (do
      let we4 ← AspisR1S9HelperP6.field.WideExact.mul low all
      let weights1 ← Array.update old 0#usize we4
      let we5 ← AspisR1S9HelperP6.field.WideExact.mul low first3
      let we6 ← AspisR1S9HelperP6.field.WideExact.mul_qm31 we5 q16
      let out ← Array.update weights1 1#usize we6
      k out) := by
  simp only [AspisR1.S9SideZeroTailRootV1.sideZeroTail,
    result_bind_assoc, bind_tc_ok]

/-- Candidate side-one old-array fragment followed by an arbitrary
continuation, flattened in exact source order. -/
theorem candidateAfterOld_bind {β : Type}
    (old ap1 : AspisR1S9CandidateSideOneTailMapV4.CA)
    (low all first2 : AspisR1S9CandidateSideOneTailMapV4.C)
    (q41 q16 : AspisR1S9CandidateSideOneTailMapV4.CQ)
    (perm3 : AspisR1S9CandidateSideOneTailMapV4.U)
    (k : AspisR1S9CandidateSideOneTailMapV4.CA → Result β) :
    (do
      let out ← AspisR1S9CandidateSideOneTailMapV4.candidateAfterOld
        old ap1 low all first2 q41 q16 perm3
      k out) =
    (do
      let we4 ← Array.index_usize old 1#usize
      let we5 ← Array.index_usize ap1 perm3
      let we6 ← AspisR1S9CandidateHelperV1.field.WideExact.mul_m31 we5
        _root_.AspisR1S9CandidateHelperV1.weights.QUARTER
      let we7 ← AspisR1S9CandidateHelperV1.field.WideExact.mul low we6
      let we8 ← AspisR1S9CandidateHelperV1.field.WideExact.add we4 we7
      let weights1 ← Array.update old 1#usize we8
      let we9 ← AspisR1S9CandidateHelperV1.field.WideExact.mul low all
      let we10 ← AspisR1S9CandidateHelperV1.field.WideExact.mul_qm31 we9 q41
      let weights2 ← Array.update weights1 2#usize we10
      let we11 ← AspisR1S9CandidateHelperV1.field.WideExact.mul low first2
      let q3 ← AspisR1S9CandidateHelperV1.field.QM31.mul q16 q41
      let we12 ← AspisR1S9CandidateHelperV1.field.WideExact.mul_qm31 we11 q3
      let out ← Array.update weights2 3#usize we12
      k out) := by
  simp only [AspisR1S9CandidateSideOneTailMapV4.candidateAfterOld,
    AspisR1S9CandidateSideOneTailMapV4.candidateAddTail,
    result_bind_assoc, bind_tc_ok]

/-- P6 side-one old-array fragment followed by an arbitrary continuation,
including its own checked PERM[3] read. -/
theorem p6AfterOld_bind {β : Type}
    (old ap1 : AspisR1S9CandidateSideOneTailMapV4.PA)
    (low all first2 : AspisR1S9CandidateSideOneTailMapV4.P)
    (q41 q16 : AspisR1S9CandidateSideOneTailMapV4.PQ)
    (k : AspisR1S9CandidateSideOneTailMapV4.PA → Result β) :
    (do
      let out ← AspisR1S9CandidateSideOneTailMapV4.p6AfterOld
        old ap1 low all first2 q41 q16
      k out) =
    (do
      let we4 ← Array.index_usize old 1#usize
      let perm3 ← Array.index_usize _root_.AspisR1S9HelperP6.weights.PERM 3#usize
      let we5 ← Array.index_usize ap1 perm3
      let we6 ← AspisR1S9HelperP6.field.WideExact.mul_m31 we5
        _root_.AspisR1S9HelperP6.weights.QUARTER
      let we7 ← AspisR1S9HelperP6.field.WideExact.mul low we6
      let we8 ← AspisR1S9HelperP6.field.WideExact.add we4 we7
      let weights1 ← Array.update old 1#usize we8
      let we9 ← AspisR1S9HelperP6.field.WideExact.mul low all
      let we10 ← AspisR1S9HelperP6.field.WideExact.mul_qm31 we9 q41
      let weights2 ← Array.update weights1 2#usize we10
      let we11 ← AspisR1S9HelperP6.field.WideExact.mul low first2
      let q3 ← AspisR1S9HelperP6.field.QM31.mul q16 q41
      let we12 ← AspisR1S9HelperP6.field.WideExact.mul_qm31 we11 q3
      let out ← Array.update weights2 3#usize we12
      k out) := by
  simp only [AspisR1S9CandidateSideOneTailMapV4.p6AfterOld,
    AspisR1S9CandidateSideOneTailMapV4.p6AddTail,
    AspisR1S9HelperP6.field.WideExact.mul_m31,
    AspisR1S9HelperP6.field.WideExact.mul,
    AspisR1S9HelperP6.field.WideExact.add,
    AspisR1S9HelperP6.field.WideExact.mul_qm31,
    AspisR1S9HelperP6.field.QM31.mul,
    result_bind_assoc, bind_tc_ok]

#print axioms result_bind_assoc
#print axioms candidateSideZeroTail_bind
#print axioms p6SideZeroTail_bind
#print axioms candidateAfterOld_bind
#print axioms p6AfterOld_bind

end AspisR1S9CandidateTailFlatBindV1
