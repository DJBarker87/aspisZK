import NKU_Chronology
import NKK_RawPrefix
set_option autoImplicit false
noncomputable section
namespace NKU_Roots
open Aeneas Aeneas.Std Result AspisR1 NID_ResumeEmission
open NKU_Chronology
/-- Native raw32 triple at the SAME checkpoint backing and cursor80. -/
def entry (s : NKU.State) : verifier.Reader := { bytes := s.frame.checkpoint, «at» := 80#usize }
def post (s : NKU.State) (roots : List (Array U8 32#usize)) (r : verifier.Reader) : NKU.State :=
 {s with phase := .fields,reader := r,decoded := {s.decoded with roots := roots}}
def run : Stage Unit := fun s => do
 let (roots,last) ← NKK_RawPrefix.run 32#usize 3 (entry s)
 pure (.Ok ((),post s roots last))
def source : Stage Unit := fun s => do
 let (roots,last) ← NKK_RawPrefix.literal 32#usize 3 (entry s)
 pure (.Ok ((),post s roots last))
theorem source_eq_run (s : NKU.State) : source s=run s := by
 unfold source run
 rw [NKK_RawPrefix.source]
theorem frame (s : NKU.State) (roots : List (Array U8 32#usize)) (r : verifier.Reader) :
 (post s roots r).frame=s.frame ∧ (post s roots r).owned=s.owned ∧
 (post s roots r).decoded.next=s.decoded.next ∧
 (post s roots r).decoded.endAt=s.decoded.endAt := ⟨rfl,rfl,rfl,rfl⟩
#print axioms source_eq_run
#print axioms frame
end NKU_Roots
