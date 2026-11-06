import NKU_Chronology
import NKK_FieldStages
set_option autoImplicit false
noncomputable section
namespace NKU_Gamma
open Aeneas Aeneas.Std Result AspisR1 NID_ResumeEmission
open NKU_Chronology
def post (s : NKU.State) (g k a0 a1 : NKU.E) (rho : NKU.K) (r : verifier.Reader) : NKU.State :=
 {s with phase := .queries,reader := r,
  decoded := {s.decoded with gammaAlpha := [g,k,a0,a1],rho := some rho}}
def reply (s : NKU.State) (g k a0 a1 : NKU.E) (rho : NKU.K) (r : verifier.Reader) :
 Run (core.result.Result (Unit × NKU.State) verifier.Error) := pure (.Ok ((),post s g k a0 a1 rho r))
/-- NKK_K013 native five-call G, with every E/K Err and abort prefix. -/
def run : Stage Unit := fun s =>
 NKK_FieldFold.program NKK_FieldSites.gammaKinds s.reader >>= NKK_FieldStages.gammaDispatch (reply s)
def source : Stage Unit := fun s=>NKK_FieldStages.gamma s.reader (reply s)
theorem source_eq_run (s : NKU.State) : source s=run s :=
 (NKK_FieldStages.gamma_source s.reader (reply s)).symm
theorem frame (s : NKU.State) (g k a0 a1 : NKU.E) (rho : NKU.K) (r : verifier.Reader) :
 (post s g k a0 a1 rho r).frame=s.frame ∧
 (post s g k a0 a1 rho r).decoded.roots=s.decoded.roots ∧
 (post s g k a0 a1 rho r).owned=s.owned := ⟨rfl,rfl,rfl⟩
#print axioms source_eq_run
#print axioms frame
end NKU_Gamma
