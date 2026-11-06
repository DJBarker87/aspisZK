import NKK_FieldFold
import NKK_LogAlgebra
import NKK_LogReduce
set_option autoImplicit false
noncomputable section
namespace NKK_FieldCps
open Aeneas Aeneas.Std Result AspisR1 NID_ResumeEmission NKK_FieldFold

def applyResult {T : Type}
 (next : List Value → Reader → NJU_Log.Run NJU_ResumeObserved.Event (core.result.Result T verifier.Error)) :
 core.result.Result (List Value × Reader) verifier.Error → NJU_Log.Run NJU_ResumeObserved.Event (core.result.Result T verifier.Error)
 | .Err err => pure (.Err err)
 | .Ok (values,r) => next values r

def cps {T : Type} : List Kind → Reader →
 (List Value → Reader → NJU_Log.Run NJU_ResumeObserved.Event (core.result.Result T verifier.Error)) →
 NJU_Log.Run NJU_ResumeObserved.Event (core.result.Result T verifier.Error)
 | [],r,next => next [] r
 | kind::kinds,r,next => do
   let (reply,last) ← call kind r
   match reply with
   | .Err err => pure (.Err err)
   | .Ok value => cps kinds last (fun values out=>next (value::values) out)

theorem map_cont {T : Type} (value : Value)
 (reply : core.result.Result (List Value × Reader) verifier.Error)
 (next : List Value → Reader → NJU_Log.Run NJU_ResumeObserved.Event (core.result.Result T verifier.Error)) :
 applyResult next (mapInner (fun x=>(value::x.1,x.2)) reply)=
 applyResult (fun values out=>next (value::values) out) reply := by
 cases reply with
 | Err err => rfl
 | Ok pair => cases pair;rfl

/-- A full field-log fold composes with the caller continuation, including
all native Err/abort prefixes. No endpoint equation or callback law assumed. -/
theorem source {T : Type} (kinds : List Kind) (r : Reader)
 (next : List Value → Reader → NJU_Log.Run NJU_ResumeObserved.Event (core.result.Result T verifier.Error)) :
 (program kinds r >>= applyResult next)=cps kinds r next := by
 induction kinds generalizing r next with
 | nil => rfl
 | cons kind kinds ih =>
  unfold program cps
  rw [NKK_LogAlgebra.bind_assoc]
  apply NKK_LogAlgebra.bind_congr
  rintro ⟨reply,last⟩
  cases reply with
  | Err err => rfl
  | Ok value =>
   simp only [NKK_LogAlgebra.bind_assoc,NKK_LogReduce.pure_bind]
   rw [←ih last (fun values out=>next (value::values) out)]
   apply NKK_LogAlgebra.bind_congr
   intro reply
   exact map_cont value reply next

#print axioms map_cont
#print axioms source
end NKK_FieldCps
