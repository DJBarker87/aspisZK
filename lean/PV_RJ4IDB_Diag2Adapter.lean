import PV_RJ4IDB_Decoder
set_option autoImplicit false
namespace PV_RJ4IDB
/-- Retain diag2's complete alphabet as its own tagged channel. In particular,
entered/rejected records are not confused with writes or removed. -/
def diag2Events (es : List PV_DIAG2.Effect) : List Event := es.map Event.diagnostic2

theorem diag2_recover (es : List PV_DIAG2.Effect) :
 diagnostics2 (diag2Events es) = es := by
 induction es with
 | nil => rfl
 | cons e es ih => change e :: diagnostics2 (diag2Events es) = e :: es; rw [ih]

theorem diag2_failure_recover (es : List PV_DIAG2.Effect) (err : Bytes) :
 (decoder (⟨diag2Events es,.failure err⟩ : Trace Unit)).errorsStderr2 = es :=
 diag2_recover es

theorem diag2_divergence_recover (es : List PV_DIAG2.Effect) :
 (decoder (⟨diag2Events es,.diverge⟩ : Trace Unit)).errorsStderr2 = es :=
 diag2_recover es

theorem diag2_append (a b : List PV_DIAG2.Effect) :
 diag2Events (a++b) = diag2Events a ++ diag2Events b := List.map_append
#print axioms diag2_recover
#print axioms diag2_failure_recover
#print axioms diag2_divergence_recover
#print axioms diag2_append
end PV_RJ4IDB
