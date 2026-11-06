import NKU_Chronology
import NJZ_Validator
set_option autoImplicit false
noncomputable section
namespace NKU_Validator
open Aeneas Aeneas.Std Result AspisR1 NID_ResumeEmission NJU_ResumeObserved
open NKU_Chronology
def values : List U32 → Result (Array U32 22#usize)
 | [q0,q1,q2,q3,q4,q5,q6,q7,q8,q9,q10,q11,q12,q13,q14,q15,q16,q17,q18,q19,q20,q21] => ok (Array.make 22#usize [q0,q1,q2,q3,q4,q5,q6,q7,q8,q9,q10,q11,q12,q13,q14,q15,q16,q17,q18,q19,q20,q21])
 | _ => fail .panic
/-- CLOSED TX2:126 at the SAME22 decoded words, every rejection retained. -/
def run : Stage Unit := fun s=>do
 let queries ← values s.decoded.queries
 let reply ← recordValidate queries
 NKK_Try.emitted reply (fun _=>pure (.Ok ((),{s with phase := .semantic})))
theorem frame (s : NKU.State) :
 ({s with phase := .semantic} : NKU.State).frame=s.frame ∧
 ({s with phase := .semantic} : NKU.State).decoded=s.decoded ∧
 ({s with phase := .semantic} : NKU.State).reader=s.reader ∧
 ({s with phase := .semantic} : NKU.State).owned=s.owned := ⟨rfl,rfl,rfl,rfl⟩
#print axioms frame
end NKU_Validator
