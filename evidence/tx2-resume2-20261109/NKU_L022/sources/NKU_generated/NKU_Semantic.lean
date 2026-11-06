import NKU_Chronology
import NKK_SectionFrames
set_option autoImplicit false
noncomputable section
namespace NKU_Semantic
open Aeneas Aeneas.Std Result AspisR1 NID_ResumeEmission NJU_ResumeObserved
open NKU_Chronology
def post (s : NKU.State) (values : Array NKU.K 10#usize) (cursor : Usize) : NKU.State :=
 {s with phase := .zClaim, reader := {s.reader with «at» := cursor}, decoded := {s.decoded with semantic := some values}}
/-- CLOSED TX2:121 complete reply, including Err and every earlier effect. -/
def run : Stage Unit := fun s => do
 let reply ← recordSemantic s.frame.checkpoint s.reader.at
 NKK_Try.emitted reply (fun (values,cursor)=>pure (.Ok ((),post s values cursor)))
theorem frame (s : NKU.State) (values : Array NKU.K 10#usize) (cursor : Usize) :
 (post s values cursor).frame=s.frame ∧
 (post s values cursor).reader.bytes=s.reader.bytes ∧
 (post s values cursor).owned=s.owned := ⟨rfl,rfl,rfl⟩
#print axioms frame
end NKU_Semantic
