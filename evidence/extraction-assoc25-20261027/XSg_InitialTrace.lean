import XSg_NewSource
import XRz_FinishOwned
open Aeneas Aeneas.Std Result XRn_Join_Release
set_option autoImplicit false
noncomputable section
namespace XSg_InitialTrace
open S7Kani3CallerTrace
/-- Exact nominal constructor-row identity. -/
theorem row (q : aspis_core.field.QM31) : XSg_NewRows.row q=initialRow (XRx_ValueOwned.oldQ q) := by rfl
/-- The source constructor supplies the actual old trace initial state. -/
theorem source (weights : Slice aspis_core.field.QM31) (b : verifier.BatchedWeights)
 (run : verifier.BatchedWeights.new weights=ok (.Ok b)) :
 PushTrace (XRz_FinishOwned.weights weights) (XRu_PushTransport.bw b)
  (initialSum (XRz_FinishOwned.weights weights)) := by
 have h := XSg_NewSource.source weights b run
 have raw : b.raw=initialRaw (XRz_FinishOwned.weights weights) := by
  apply Subtype.ext
  rw [h.1]
  change weights.val.map XSg_NewRows.row=(weights.val.map XRx_ValueOwned.oldQ).map initialRow
  rw [List.map_map]
  exact List.map_congr_left (by intro q _;exact row q)
 have same : XRu_PushTransport.bw b=⟨initialRaw (XRz_FinishOwned.weights weights),0#usize⟩ := by
  cases b
  simp only [XRu_PushTransport.bw] at *
  cases raw
  cases h.2
  rfl
 rw [same]
 exact PushTrace.initial
#print axioms row
#print axioms source
end XSg_InitialTrace
