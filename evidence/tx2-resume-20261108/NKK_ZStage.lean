import NKK_FieldStages
set_option autoImplicit false
noncomputable section
namespace NKK_ZStage
open Aeneas Aeneas.Std Result AspisR1 NID_ResumeEmission NKK_FieldFold NKK_FieldStages

def source {T : Type} (r : Reader)
 (next : K → K → K → K → E → E → K → Reader → NJU_Log.Run NJU_ResumeObserved.Event (core.result.Result T verifier.Error)) :=
 withK r fun x0 r1=>withK r1 fun y0 r2=>withK r2 fun x1 r3=>withK r3 fun y1 r4=>
 withE r4 fun claim r5=>withE r5 fun rhs r6=>withK r6 fun power r7=>next x0 y0 x1 y1 claim rhs power r7

def dispatch {T : Type}
 (next : K → K → K → K → E → E → K → Reader → NJU_Log.Run NJU_ResumeObserved.Event (core.result.Result T verifier.Error)) :=
 NKK_FieldCps.applyResult (fun values r=>match values with
 | [.k x0,.k y0,.k x1,.k y1,.e claim,.e rhs,.k power] => next x0 y0 x1 y1 claim rhs power r
 | _ => liftM (Result.fail .panic))

/-- Native z/claim/rhs/power G feeds the SAME following allocation site. -/
theorem source_eq_model {T : Type} (r : Reader)
 (next : K → K → K → K → E → E → K → Reader → NJU_Log.Run NJU_ResumeObserved.Event (core.result.Result T verifier.Error)) :
 (program NKK_FieldSites.zKinds r >>= dispatch next)=source r next := by
 unfold dispatch
 rw [NKK_FieldCps.source]
 unfold source NKK_FieldSites.zKinds
 simp only [NKK_FieldCps.cps,NKK_FieldLiteral.call_k,NKK_FieldLiteral.call_e,
  NKK_LogAlgebra.bind_assoc,NKK_LogReduce.pure_bind,withE,withK,NKK_Try.branch]
 repeat' first
 | rfl
 | (apply NKK_LogAlgebra.bind_congr;rintro ⟨reply,last⟩;cases reply)
 | (fail_if_no_progress simp only [mapInner,NKK_LogReduce.pure_bind])

#print axioms source_eq_model
end NKK_ZStage
