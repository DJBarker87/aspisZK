import RRActualScalarTraceBoundsM10
import RRReachableStorageM10
import RRNodeTariffM10

/-! Field and normalization envelopes on the actual sequential RR cursor.
The bounds apply to stored rows, including padded and fallback states. -/
set_option autoImplicit false
noncomputable section
namespace AspisR1.RRActualFieldEnvelopeM10
open CompPoly RRConcreteState RRConcreteValidState RRConcreteTraversal
open GSScalarCallScheduleM10
variable {K : Type} [Field K] [BEq K] [LawfulBEq K] [DecidableEq K] [Fintype K]

def node (D ell q t : Nat) (s : ValidState ell K)
    (H : Nat → Fin t → K × K) (cursor : Nat) : Nat :=
  let r := GSScalarAtCursorM10.general (scalarPolynomial s.val) q t H cursor
  GSScalarTraceFieldWorkM10.traceWork ell r.2+
    ((r.1.1.getD []).map (fun a => (RRNormalizationWorkM10.normalize D ell s.val a).2)).sum+
    100*(D+1)^2

theorem roots_length (ell q t : Nat) (s : ValidState ell K)
    (H : Nat → Fin t → K × K) (cursor : Nat) (hq : q = Fintype.card K) :
    ((GSScalarAtCursorM10.general (scalarPolynomial s.val) q t H cursor).1.1.getD []).length ≤ ell := by
  have hs := SequentialProgramInvariants.all_eval H _ _
    (SequentialProgramInvariants.all_sequential _ _
      (CompPolyGeneralRootsProgram.generalRoots_correct (scalarPolynomial s.val) q t hq
        (scalar_nonzero ell s)) cursor)
  have hv := congrArg Prod.fst (GSScalarAtCursorM10.value (scalarPolynomial s.val) q t H cursor)
  dsimp only at hv
  have hs := hs.2
  rw [← hv] at hs
  have hd : (scalarPolynomial s.val).toPoly.natDegree ≤ ell := by
    rw [scalarPolynomial_toPoly]
    exact s.property.2 0 (Nat.zero_le _)
  cases ho : (GSScalarAtCursorM10.general (scalarPolynomial s.val) q t H cursor).1.1 with
  | none => exact Nat.zero_le _
  | some roots => exact ((hs roots ho).2.2).trans hd

theorem node_bound (D ell q t : Nat) (s : ValidState ell K)
    (H : Nat → Fin t → K × K) (cursor : Nat) (hq : q = Fintype.card K)
    (hell : 1 ≤ ell) (hD : s.val.maxX+ell ≤ D)
    (hw : ∀ row ∈ s.val.rows, row.length ≤ D) :
    node D ell q t s H cursor ≤ RRNodeTariffM10.tariff D ell q t := by
  have hd : (scalarPolynomial s.val).toPoly.natDegree ≤ ell := by
    rw [scalarPolynomial_toPoly]
    exact s.property.2 0 (Nat.zero_le _)
  have hf := GSScalarAtBoundsM10.field_work (scalarPolynomial s.val) q t ell H cursor hd hell
  have hn := RawExtractorCostLedger.sum_charge_le
    ((GSScalarAtCursorM10.general (scalarPolynomial s.val) q t H cursor).1.1.getD [])
    (fun a => (RRNormalizationWorkM10.normalize D ell s.val a).2)
    ell (RRNormalizationWorkM10.budget D) (roots_length ell q t s H cursor hq)
    (fun a _ => RRNormalizationWorkM10.normalize_work D ell s.val a hD hw)
  exact Nat.add_le_add_right (Nat.add_le_add hf hn) _

theorem scalar_work (ell q t d : Nat) (s : ValidState ell K)
    (H : Nat → Fin t → K × K) (cursor : Nat) (hq : q = Fintype.card K)
    (hell : 1 ≤ ell) :
    GSScalarTraceFieldWorkM10.traceWork ell
      (RRActualScalarTraceM10.collect ell q t H d s cursor).2 ≤
      RRActualScalarTraceBoundsM10.budget ell t d*GSScalarTraceFieldWorkM10.callBudget ell q :=
  GSScalarTraceFieldWorkM10.trace_work _ ell q _
    (RRActualScalarTraceBoundsM10.length ell q t H d s cursor hq)
    (RRActualScalarTraceBoundsM10.bounded ell q t H d s cursor hell)

theorem reachable_node (ell D d q t : Nat) (start : RawState K)
    (hb : RRReachableStorageM10.BoundedRows D start)
    {n : Nat} (s : ValidState ell K)
    (hr : RRReachableStorageM10.Reachable ell start n s.val) (hn : n ≤ d)
    (H : Nat → Fin t → K × K) (cursor : Nat) (hq : q = Fintype.card K)
    (hell : 1 ≤ ell) :
    node (D+(d+1)*(ell+1)+1) ell q t s H cursor ≤
      RRNodeTariffM10.tariff (D+(d+1)*(ell+1)+1) ell q t := by
  have hu := RRReachableStorageM10.reachable_bound ell D start hb hr
  have hm := Nat.mul_le_mul_right (ell+1) hn
  have hx := hu.1
  have he : d*(ell+1)+(ell+1) = (d+1)*(ell+1) := by ring
  apply node_bound _ _ _ _ _ _ _ hq hell
  · omega
  · intro row hr
    have hh := hu.2.2 row hr
    omega

#print axioms roots_length
#print axioms node_bound
#print axioms scalar_work
#print axioms reachable_node
end AspisR1.RRActualFieldEnvelopeM10
end
