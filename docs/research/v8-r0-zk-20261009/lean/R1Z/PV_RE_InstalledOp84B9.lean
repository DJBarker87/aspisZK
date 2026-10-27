import R1Z.PV_CB_CandidateCore
import R1Z.PV_RE_NoCatchCore
set_option autoImplicit false
noncomputable section
namespace R1Z.PV_RE_InstalledOp84B9
open Aeneas Aeneas.Std Result ProverRwFull

/-- Explicit source-equality composition avoids rewriting beneath the pending
lambda. The original failed InstalledOp84 candidate remains unchanged. -/
theorem installed_noCatch (base : ExternalTypes)
    (ops : @ExternalFuns (PV_CB_CandidateDictionary.native base))
    (tag : U8) (values : Slice U8) :
    PV_RE_NoCatchCore.NoCatch (fun pending : Result (Array U8 32#usize) =>
      (PV_CB_CandidateDictionary.selected base ops).op84
        (fun _ => pending) tag values) := by
  constructor
  · intro e
    exact (PV_CB_CandidateDictionary.op84 base ops (fun _ => .fail e) tag values).trans rfl
  · exact (PV_CB_CandidateDictionary.op84 base ops (fun _ => .div) tag values).trans rfl

#print installed_noCatch
#print axioms installed_noCatch
end R1Z.PV_RE_InstalledOp84B9
