import GSScalarTraceFieldWorkM10
import RRNormalizationWorkM10
import RRConcreteTraversal

/-! Local RR node envelope from the actual scalar trace and every returned
root's complete row normalization. This pays failed scalar retries too.
The field/control tariff is separate from its eventual bit/slot lift. -/
set_option autoImplicit false
noncomputable section
namespace AspisR1.RRNodeTariffM10
open CompPoly RRConcreteState RRConcreteValidState RRConcreteTraversal
open GSScalarCallScheduleM10 SequentialProgramInvariants
open AspisV8R19.MemoizedProgramLaw
variable {K : Type} [Field K] [BEq K] [LawfulBEq K] [DecidableEq K] [Fintype K]

def nodeWork (D ell q t : Nat) (s : ValidState ell K) (H : Nat → Fin t → K × K) : Nat :=
  let r := GSScalarSequentialScheduleM10.general (scalarPolynomial s.val) q t H
  GSScalarTraceFieldWorkM10.traceWork ell r.2+
    ((r.1.1.getD []).map (fun a => (RRNormalizationWorkM10.normalize D ell s.val a).2)).sum+
    100*(D+1)^2

def tariff (D ell q t : Nat) : Nat :=
  (2+fuelBudget t (ell+1))*GSScalarTraceFieldWorkM10.callBudget ell q+
    ell*RRNormalizationWorkM10.budget D+100*(D+1)^2

theorem roots_length (ell q t : Nat) (s : ValidState ell K)
    (H : Nat → Fin t → K × K) (hq : q = Fintype.card K) :
    ((GSScalarSequentialScheduleM10.general (scalarPolynomial s.val) q t H).1.1.getD []).length ≤ ell := by
  have hs := all_eval H _ _ (CompPolyGeneralRootsProgram.generalRoots_correct
    (scalarPolynomial s.val) q t hq (scalar_nonzero ell s))
  rw [← GSScalarSequentialScheduleM10.general_value] at hs
  have hd : (scalarPolynomial s.val).toPoly.natDegree ≤ ell := by
    rw [scalarPolynomial_toPoly]
    exact s.property.2 0 (Nat.zero_le _)
  cases ho : (GSScalarSequentialScheduleM10.general (scalarPolynomial s.val) q t H).1.1 with
  | none => exact Nat.zero_le _
  | some roots => exact ((hs.2 roots ho).2.2).trans hd

theorem work (D ell q t : Nat) (s : ValidState ell K) (H : Nat → Fin t → K × K)
    (hq : q = Fintype.card K) (hell : 1 ≤ ell)
    (hD : s.val.maxX+ell ≤ D) (hw : ∀ row ∈ s.val.rows, row.length ≤ D) :
    nodeWork D ell q t s H ≤ tariff D ell q t := by
  have hd : (scalarPolynomial s.val).toPoly.natDegree ≤ ell := by
    rw [scalarPolynomial_toPoly]
    exact s.property.2 0 (Nat.zero_le _)
  have hs := GSScalarTraceFieldWorkM10.general_work (scalarPolynomial s.val) q t ell H hd hell
  have hr := roots_length ell q t s H hq
  have hn := RawExtractorCostLedger.sum_charge_le
    ((GSScalarSequentialScheduleM10.general (scalarPolynomial s.val) q t H).1.1.getD [])
    (fun a => (RRNormalizationWorkM10.normalize D ell s.val a).2)
    ell (RRNormalizationWorkM10.budget D) hr
    (fun a _ => RRNormalizationWorkM10.normalize_work D ell s.val a hD hw)
  exact Nat.add_le_add_right (Nat.add_le_add hs hn) _

#print axioms roots_length
#print axioms work
end AspisR1.RRNodeTariffM10
end
