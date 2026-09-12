import SameBodySequentialCodec
import FSV7OODBodyScript
import OODInterpolantRows
import AspisFormal.K1.V7Tag73SecureCircleMap

/-!
# OOD interpolant data from one sampled pair and one canonical body

This executable constructor decodes both sampled circle coordinates, parses
the 697 canonical fixed fields once, reads the two actual 29-lane OOD rows,
and computes the selected-coordinate inverse.  Every failure is `none`; no
caller supplies `OODInterpolant.Data` or its `Checked` proof.

The separate chronological sampler theorem must still prove that its returned
point bytes reach this decoder, and literal Rust parsing/inversion refinement
remains open.
-/

set_option autoImplicit false
set_option Elab.async false
set_option maxHeartbeats 200000

namespace AspisV8Completion.SameBodyOODData

open AspisV5ComponentCQM31Representation
open AspisV5ComponentCQM31TowerExact
open AspisK1.V7Tag73DeterministicRefinement
open AspisK1.V7Tag73SecureCircleMap
open AspisV8.OODInterpolant
open AspisV8.SameBodySequentialCodec

abbrev Bytes := List UInt8
abbrev K := QM31Exact
abbrev Point := FSV7OODBodyScript.Point
abbrev OODResult := FSV7OODBodyScript.Result

noncomputable section

theorem inverse_result_checked (data : Data (K := K))
    (success : qm31TryInv (data.h0 - data.h1) = some data.inverse) :
    data.Checked := by
  classical
  have nonzero : data.h0 - data.h1 ≠ 0 := by
    intro zero
    rw [zero, qm31TryInv_eq] at success
    simp at success
  have inverse : (data.h0 - data.h1)⁻¹ = data.inverse := by
    rw [qm31TryInv_eq, if_neg nonzero] at success
    exact Option.some.inj success
  change (data.h0 - data.h1) * data.inverse = 1
  rw [← inverse]
  exact mul_inv_cancel₀ nonzero

def decodePointCoordinates (point : Point) : Option (K × K) := do
  let x ← decodeTagQM31ExactLE point.x
  let y ← decodeTagQM31ExactLE point.y
  pure (x, y)

def answerIndex (sample : Fin 2) (lane : Fin 29) : Nat :=
  359 + 29 * sample.val + lane.val

def answerRows (values : List K) : Fin 2 → Fin 29 → K :=
  fun sample lane => values.getD (answerIndex sample lane) 0

/-- Total executable constructor with fail-closed coordinate, body and inverse
decoding. -/
def fromSampled (out : OODResult) (gamma : K) (body : Bytes) : Option (Data (K := K)) := do
  let first ← decodePointCoordinates out.first
  let second ← decodePointCoordinates out.second
  let values ← fields (body.map UInt8.toFin)
  let useX := decide (first.1 ≠ second.1)
  let h0 := if useX then first.1 else first.2
  let h1 := if useX then second.1 else second.2
  let inverse ← qm31TryInv (h0 - h1)
  pure {
    x0 := first.1
    y0 := first.2
    x1 := second.1
    y1 := second.2
    gamma := gamma
    answers := answerRows values
    inverse := inverse }

theorem fromSampled_checked (out : OODResult) (gamma : K) (body : Bytes)
    (data : Data (K := K)) (success : fromSampled out gamma body = some data) :
    data.Checked := by
  rcases firstEq : decodePointCoordinates out.first with _ | first
  · simp [fromSampled, firstEq] at success
  rcases secondEq : decodePointCoordinates out.second with _ | second
  · simp [fromSampled, firstEq, secondEq] at success
  rcases valuesEq : fields (body.map UInt8.toFin) with _ | values
  · simp [fromSampled, firstEq, secondEq, valuesEq] at success
  rcases inverseEq : qm31TryInv
      ((if first.1 = second.1 then first.2 else first.1) -
       (if first.1 = second.1 then second.2 else second.1)) with _ | inverse
  · simp [fromSampled, firstEq, secondEq, valuesEq, inverseEq] at success
  have same : data = {
      x0 := first.1, y0 := first.2, x1 := second.1, y1 := second.2,
      gamma := gamma, answers := answerRows values, inverse := inverse } := by
    simpa [fromSampled, firstEq, secondEq, valuesEq, inverseEq] using success.symm
  subst data
  apply inverse_result_checked
  simpa [Data.h0, Data.h1, Data.useX, selected] using inverseEq

theorem fromSampled_body_canonical (out : OODResult) (gamma : K) (body : Bytes)
    (data : Data (K := K)) (success : fromSampled out gamma body = some data) :
    ∃ values, fields (body.map UInt8.toFin) = some values ∧
      data.answers = answerRows values := by
  rcases firstEq : decodePointCoordinates out.first with _ | first
  · simp [fromSampled, firstEq] at success
  rcases secondEq : decodePointCoordinates out.second with _ | second
  · simp [fromSampled, firstEq, secondEq] at success
  rcases valuesEq : fields (body.map UInt8.toFin) with _ | values
  · simp [fromSampled, firstEq, secondEq, valuesEq] at success
  rcases inverseEq : qm31TryInv
      ((if first.1 = second.1 then first.2 else first.1) -
       (if first.1 = second.1 then second.2 else second.1)) with _ | inverse
  · simp [fromSampled, firstEq, secondEq, valuesEq, inverseEq] at success
  have same : data = {
      x0 := first.1, y0 := first.2, x1 := second.1, y1 := second.2,
      gamma := gamma, answers := answerRows values, inverse := inverse } := by
    simpa [fromSampled, firstEq, secondEq, valuesEq, inverseEq] using success.symm
  subst data
  exact ⟨values, rfl, rfl⟩

theorem fromSampled_gamma (out : OODResult) (gamma : K) (body : Bytes)
    (data : Data (K := K)) (success : fromSampled out gamma body = some data) :
    data.gamma = gamma := by
  rcases firstEq : decodePointCoordinates out.first with _ | first
  · simp [fromSampled, firstEq] at success
  rcases secondEq : decodePointCoordinates out.second with _ | second
  · simp [fromSampled, firstEq, secondEq] at success
  rcases valuesEq : fields (body.map UInt8.toFin) with _ | values
  · simp [fromSampled, firstEq, secondEq, valuesEq] at success
  rcases inverseEq : qm31TryInv
      ((if first.1 = second.1 then first.2 else first.1) -
       (if first.1 = second.1 then second.2 else second.1)) with _ | inverse
  · simp [fromSampled, firstEq, secondEq, valuesEq, inverseEq] at success
  have same : data = {
      x0 := first.1, y0 := first.2, x1 := second.1, y1 := second.2,
      gamma := gamma, answers := answerRows values, inverse := inverse } := by
    simpa [fromSampled, firstEq, secondEq, valuesEq, inverseEq] using success.symm
  subst data
  rfl

#print axioms fromSampled_checked
#print axioms fromSampled_body_canonical
#print axioms fromSampled_gamma

end
end AspisV8Completion.SameBodyOODData
