import NKU_Success
set_option autoImplicit false
noncomputable section
namespace NKU_Core
open Aeneas Aeneas.Std Result AspisR1 NID_ResumeEmission
open NKU_Chronology
/-- Full live parent data except the control-phase label. -/
def value (s : NKU.State) := (s.frame,s.decoded,s.reader,s.iterator,s.owned,s.returned,s.history)
def Preserves (step : Stage Unit) : Prop :=
 ∀ s out,(step s).result=ok (.Ok ((),out)) → value out=value s
/-- Frame chaining uses the first cut's actual post, not an existential seed. -/
theorem bind (a b : Stage Unit) (ha : Preserves a) (hb : Preserves b) :
 Preserves (NKU_Chronology.bind a (fun _=>b)) := by
 intro s out actual
 unfold NKU_Chronology.bind at actual
 rw [NJU_Log.erase_bind] at actual
 cases head : (a s).result with
 | fail err => rw [head] at actual;cases actual
 | div => rw [head] at actual;cases actual
 | ok reply =>
  rw [head] at actual
  cases reply with
  | Err err => cases actual
  | Ok pair =>
   rcases pair with ⟨unit,middle⟩
   cases unit
   exact (hb middle out actual).trans (ha s middle head)
#print axioms bind
end NKU_Core
