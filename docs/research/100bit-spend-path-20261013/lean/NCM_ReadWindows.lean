import NCM_PartsWindows

set_option autoImplicit false
namespace AspisR1.NCM_ReadWindows
open Aeneas Aeneas.Std Result CheckpointBytes5Effect

/-- A single physical call with exact argument windows and unchanged reply
appends exactly its actual event on an arbitrary prior log, including a
rejecting caller's prefix. Call-site/source association is not assumed here. -/
theorem observation {X : Type} (D : AspisR1Stage2.aspis_core.digest.Digest32 X)
    (hash : X) (actual expected : Parts) (reply : Digest) (before : Log)
    (arity : actual.val.length=expected.val.length)
    (sizes : ∀ j, j<expected.val.length →
      (actual.val[j]!).val.length=(expected.val[j]!).val.length)
    (windows : ∀ j, j<expected.val.length → ∀ i, i<(expected.val[j]!).val.length →
      (actual.val[j]!).val[i]! = (expected.val[j]!).val[i]!)
    (returned : D.digest hash actual=ok reply) :
    run D hash (.read expected .done) before=ok (reply,before++[(actual,reply)]) := by
  have args := NCM_PartsWindows.exact actual expected arity sizes windows
  rw [←args]
  simp only [run,returned,bind_tc_ok]

#print axioms observation
end AspisR1.NCM_ReadWindows
