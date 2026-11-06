import NKU_Chronology
import NKK_SectionFrames
set_option autoImplicit false
noncomputable section
namespace NKU_Weights
open Aeneas Aeneas.Std Result AspisR1 NID_ResumeEmission NJU_ResumeObserved
open NKU_Chronology
def post (s : NKU.State) (owner : alloc.vec.Vec NKU.K) (cursor : Usize) : NKU.State :=
 {s with phase := .tail,owned := some owner,reader := {s.reader with «at» := cursor}}
/-- CLOSED TX2:122, invoked on the SAME allocation received at filled44.
Complete child Result is used; native ownership/error/Drop frame is retained. -/
def run : Stage Unit := fun s=>match s.owned with
 | none => liftM (Result.fail .panic)
 | some before => do
   let reply ← recordWeights s.frame.checkpoint s.reader.at before
   NKK_Try.emitted reply (fun (owner,cursor)=>pure (.Ok ((),post s owner cursor)))
theorem frame (s : NKU.State) (owner : alloc.vec.Vec NKU.K) (cursor : Usize) :
 (post s owner cursor).frame=s.frame ∧ (post s owner cursor).decoded=s.decoded ∧
 (post s owner cursor).reader.bytes=s.reader.bytes := ⟨rfl,rfl,rfl⟩
#print axioms frame
end NKU_Weights
