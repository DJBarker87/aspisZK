import NKU_Chronology
import NKK_QueryStage
set_option autoImplicit false
noncomputable section
namespace NKU_QueryMid
open Aeneas Aeneas.Std Result AspisR1 NID_ResumeEmission
open NKU_Chronology
def post (s : NKU.State) (qs : List U32) (r : verifier.Reader) : NKU.State :=
 {s with phase := .queries,reader := r,decoded := {s.decoded with queries := s.decoded.queries++qs}}
/-- SAME native query window and Reader post-state; no suffix on abort. -/
def run : Stage Unit := fun s => do
 let (qs,last) ← NKK_QueryStage.model8 s.reader
 pure (.Ok ((),post s qs last))
def source : Stage Unit := fun s => do
 let (qs,last) ← NKK_QueryStage.source8 s.reader
 pure (.Ok ((),post s qs last))
theorem source_eq_run (s : NKU.State) : source s=run s := by
 unfold source run
 rw [NKK_QueryStage.stage8]
theorem frame (s : NKU.State) (qs : List U32) (r : verifier.Reader) :
 (post s qs r).frame=s.frame ∧
 (post s qs r).decoded.roots=s.decoded.roots ∧
 (post s qs r).decoded.gammaAlpha=s.decoded.gammaAlpha ∧
 (post s qs r).decoded.rho=s.decoded.rho ∧
 (post s qs r).owned=s.owned := ⟨rfl,rfl,rfl,rfl,rfl⟩
#print axioms source_eq_run
#print axioms frame
end NKU_QueryMid
