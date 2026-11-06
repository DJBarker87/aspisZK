import NHF_ViewInstalled
set_option autoImplicit false
noncomputable section
namespace AspisR1.NLJ_ViewCaller
open Aeneas Aeneas.Std Result AspisR1CurrentCaller InstalledPreparation
/-- CLOSED095 carries the exact semantic/y1 arguments to the installed View;
no hash equality, pointer equality or independent selected view is used. -/
theorem fields (proof semantic y1 : Slice U8) (size : 10055 ≤ proof.val.length)
 (v : verifier.View) (produced : sourceView proof semantic y1 = ok (.Ok v)) :
 v.semantic = semantic ∧ v.y1 = y1 := by
 rw [NHF_ViewInstalled.result proof semantic y1 size] at produced
 unfold NHF_ViewInstalled.port NHF_ViewResult.model at produced
 split at produced
 · cases produced
 · cases produced
   exact ⟨rfl,rfl⟩
/-- Exact native137 byte-length domain follows from the same expanded buffer,
not an extra restriction on an independently chosen semantic allocation. -/
theorem semantic_domain (proof semantic y1 : Slice U8) (size : 10055 ≤ proof.val.length)
 (v : verifier.View) (produced : sourceView proof semantic y1 = ok (.Ok v))
 (expanded : semantic.val.length = 13831) : v.semantic.val.length = 13831 := by
 rw [(fields proof semantic y1 size v produced).1]
 exact expanded
#print axioms fields
#print axioms semantic_domain
end AspisR1.NLJ_ViewCaller
end
