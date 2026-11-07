import NMT_R2_ValidatorTotal
import NMT_R2_ConcreteS1
import NMT_R2_EmittedData
set_option autoImplicit false
noncomputable section
namespace NMT_R2_ValidatorObservation
open Aeneas Aeneas.Std NMT_345 RSL NMT_R2_EmittedData

def run (st : Statement) : Obs (Except ProgramError Unit) :=
 observe id (mapOuter (mapCore id (fun _ : FormatError => (.InvalidAccountData : PE))) (validateCall st))

theorem law (st : Statement) (env : Env) :
 RS.check (!NMT_R2_PublicLibrary.valid st) .invalidAccountData env (run st) := by
 unfold run NMT_R2_PublicLibrary.valid
 rw [NMT_R2_ValidatorTotal.emitted]
 cases NMT_R2_ValidatorTotal.fresh st with
 | Ok u => cases u; rfl
 | Err e => rfl
#print axioms law
end NMT_R2_ValidatorObservation
end
