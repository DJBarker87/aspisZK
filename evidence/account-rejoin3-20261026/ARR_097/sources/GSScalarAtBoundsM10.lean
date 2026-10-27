import GSScalarAtCursorM10

set_option autoImplicit false
noncomputable section
namespace AspisR1.GSScalarAtBoundsM10
open CompPoly GSScalarCallScheduleM10
variable {K : Type} [Field K] [BEq K] [LawfulBEq K] [DecidableEq K] [Fintype K]

def budget (t D : Nat) : Nat := 2+fuelBudget t (D+1)

theorem length (p : CPolynomial K) (q t D : Nat) (H : Nat → Fin t → K × K)
    (cursor : Nat) (hd : p.toPoly.natDegree ≤ D) :
    (GSScalarAtCursorM10.general p q t H cursor).2.length ≤ budget t D := by
  have hn : (CPolynomial.monicNormalize p).natDegree ≤ D := by
    rw [CPolynomial.natDegree_toPoly,CompPolyGeneralRootsProgram.normalized_natDegree]
    exact hd
  have h := (GSScalarAtCursorM10.roots_length (CPolynomial.monicNormalize p) q t H cursor).trans
    (Nat.add_le_add_left (GSScalarSequentialScheduleM10.fuelBudget_mono t _ _
      (Nat.add_le_add_right hn 1)) 2)
  simp only [GSScalarAtCursorM10.general]
  split
  · exact Nat.zero_le _
  · split
    · exact Nat.zero_le _
    · exact h

theorem field_work (p : CPolynomial K) (q t D : Nat) (H : Nat → Fin t → K × K)
    (cursor : Nat) (hd : p.toPoly.natDegree ≤ D) (hD : 1 ≤ D) :
    GSScalarTraceFieldWorkM10.traceWork D (GSScalarAtCursorM10.general p q t H cursor).2 ≤
      budget t D*GSScalarTraceFieldWorkM10.callBudget D q :=
  GSScalarTraceFieldWorkM10.trace_work _ D q _ (length p q t D H cursor hd)
    (GSScalarAtCursorM10.bounded p q t D H cursor hd hD)

#print axioms length
#print axioms field_work
end AspisR1.GSScalarAtBoundsM10
end
