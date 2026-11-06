import NKU_Chronology
import NKK_ZStage
set_option autoImplicit false
noncomputable section
namespace NKU_ZClaim
open Aeneas Aeneas.Std Result AspisR1 NID_ResumeEmission
open NKU_Chronology
def post (s : NKU.State) (x0 y0 x1 y1 : NKU.K) (claim rhs : NKU.E) (power : NKU.K)
 (r : verifier.Reader) : NKU.State :=
 {s with phase := .filled,reader := r, decoded := {s.decoded with z := [x0,y0,x1,y1],claim := some claim,rhs := some rhs,power := some power}}
def reply (s : NKU.State) (x0 y0 x1 y1 : NKU.K) (claim rhs : NKU.E) (power : NKU.K)
 (r : verifier.Reader) : Run (core.result.Result (Unit × NKU.State) verifier.Error) :=
 pure (.Ok ((),post s x0 y0 x1 y1 claim rhs power r))
/-- NKK_K016 native seven-call G; SAME preceding state and every Err prefix. -/
def run : Stage Unit := fun s=>
 NKK_FieldFold.program NKK_FieldSites.zKinds s.reader >>= NKK_ZStage.dispatch (reply s)
def source : Stage Unit := fun s=>NKK_ZStage.source s.reader (reply s)
theorem source_eq_run (s : NKU.State) : source s=run s :=
 (NKK_ZStage.source_eq_model s.reader (reply s)).symm
theorem frame (s : NKU.State) (x0 y0 x1 y1 : NKU.K) (claim rhs : NKU.E) (power : NKU.K)
 (r : verifier.Reader) : (post s x0 y0 x1 y1 claim rhs power r).frame=s.frame ∧
 (post s x0 y0 x1 y1 claim rhs power r).decoded.semantic=s.decoded.semantic ∧
 (post s x0 y0 x1 y1 claim rhs power r).owned=s.owned := ⟨rfl,rfl,rfl⟩
#print axioms source_eq_run
#print axioms frame
end NKU_ZClaim
