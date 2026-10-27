import XRx_FinishStep
open Aeneas Aeneas.Std Result XRn_Join_Release
set_option autoImplicit false
namespace XRx_FinishRaw
/-- Terms determine push flushes, but do not change final reduction. -/
theorem value (b : verifier.BatchedWeights) (terms i : Usize) :
 verifier.BatchedWeights.value {b with terms:=terms} i=
 verifier.BatchedWeights.value b i := rfl

theorem body (b : verifier.BatchedWeights) (terms : Usize)
 (it : XRx_FinishStep.It) (back : XRx_FinishStep.Back) :
 verifier.BatchedWeights.finish_loop.body {b with terms:=terms} it back=
 verifier.BatchedWeights.finish_loop.body b it back := by
 unfold verifier.BatchedWeights.finish_loop.body
 simp only [value]

theorem loop (b : verifier.BatchedWeights) (terms : Usize)
 (it : XRx_FinishStep.It) (back : XRx_FinishStep.Back) :
 verifier.BatchedWeights.finish_loop it back {b with terms:=terms}=
 verifier.BatchedWeights.finish_loop it back b := by
 unfold verifier.BatchedWeights.finish_loop
 congr 1
 funext state
 exact body b terms state.1 state.2

/-- Complete Result equality, including every failing or divergent suffix. -/
theorem source (b : verifier.BatchedWeights) (terms : Usize)
 (weights : Slice aspis_core.field.QM31) :
 verifier.BatchedWeights.finish {b with terms:=terms} weights=
 verifier.BatchedWeights.finish b weights := by
 unfold verifier.BatchedWeights.finish
 congr 1
 funext im
 congr 1
 funext it
 rw [loop]
#print axioms value
#print axioms body
#print axioms loop
#print axioms source
end XRx_FinishRaw
