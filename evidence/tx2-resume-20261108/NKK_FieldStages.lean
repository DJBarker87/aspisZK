import NKK_FieldLiteral
import NKK_FieldCps
import NKK_FieldSites
import NKK_Try
set_option autoImplicit false
noncomputable section
namespace NKK_FieldStages
open Aeneas Aeneas.Std Result AspisR1 NID_ResumeEmission NKK_FieldFold
abbrev K := aspis_core.field.QM31
abbrev E := aspis_core.field.wide_exact.WideExact

def withE {T : Type} (r : Reader) (next : E → Reader → NJU_Log.Run NJU_ResumeObserved.Event (core.result.Result T verifier.Error)) := do
 let (reply,last) ← NJU_ResumeObserved.recordE r
 NKK_Try.emitted reply (fun value=>next value last)

def withK {T : Type} (r : Reader) (next : K → Reader → NJU_Log.Run NJU_ResumeObserved.Event (core.result.Result T verifier.Error)) := do
 let (reply,last) ← NJU_ResumeObserved.recordK r
 NKK_Try.emitted reply (fun value=>next value last)

def gamma {T : Type} (r : Reader)
 (next : E → E → E → E → K → Reader → NJU_Log.Run NJU_ResumeObserved.Event (core.result.Result T verifier.Error)) :=
 withE r fun g r1=>withE r1 fun k r2=>withE r2 fun a0 r3=>withE r3 fun a1 r4=>withK r4 fun rho r5=>next g k a0 a1 rho r5

def gammaDispatch {T : Type}
 (next : E → E → E → E → K → Reader → NJU_Log.Run NJU_ResumeObserved.Event (core.result.Result T verifier.Error)) :=
 NKK_FieldCps.applyResult (fun values r=>match values with
 | [.e g,.e k,.e a0,.e a1,.k rho] => next g k a0 a1 rho r
 | _ => liftM (Result.fail .panic))

/-- Source-ordered5-call native gamma G, followed by this exact continuation. -/
theorem gamma_source {T : Type} (r : Reader)
 (next : E → E → E → E → K → Reader → NJU_Log.Run NJU_ResumeObserved.Event (core.result.Result T verifier.Error)) :
 (program NKK_FieldSites.gammaKinds r >>= gammaDispatch next)=gamma r next := by
 change (program NKK_FieldSites.gammaKinds r >>= NKK_FieldCps.applyResult
  (fun values out=>match values with
   | [.e g,.e k,.e a0,.e a1,.k rho]=>next g k a0 a1 rho out
   | _=>liftM (Result.fail .panic)))=_
 rw [NKK_FieldCps.source]
 unfold gamma NKK_FieldSites.gammaKinds
 simp only [NKK_FieldCps.cps,NKK_FieldLiteral.call_k,NKK_FieldLiteral.call_e,
  NKK_LogAlgebra.bind_assoc,NKK_LogReduce.pure_bind,withE,withK,NKK_Try.branch]
 repeat' first
 | rfl
 | (apply NKK_LogAlgebra.bind_congr;rintro ⟨reply,last⟩;cases reply)
 | (fail_if_no_progress simp only [mapInner,NKK_LogReduce.pure_bind])

#print axioms gamma_source
end NKK_FieldStages
