-- Installed-cohort candidate; h5/h5-prime resolutions recorded in resume7.
-- This is the installed instance, not the arbitrary ExternalFuns interface.
import R1Z.PV_CB_CandidateCore
import R1Z.PV_RE_NoCatchCore
set_option autoImplicit false
noncomputable section
namespace R1Z.PV_RE_InstalledOp84
open Aeneas Aeneas.Std Result ProverRwFull

theorem installed_noCatch (base : ExternalTypes)
    (ops : @ExternalFuns (PV_CB_CandidateDictionary.native base))
    (tag : U8) (values : Slice U8) :
    PV_RE_NoCatchCore.NoCatch (fun pending : Result (Array U8 32#usize) =>
      (PV_CB_CandidateDictionary.selected base ops).op84
        (fun _ => pending) tag values) := by
  constructor
  · intro e
    rw [PV_CB_CandidateDictionary.op84]
    rfl
  · rw [PV_CB_CandidateDictionary.op84]
    rfl

#print installed_noCatch
#print axioms installed_noCatch
end R1Z.PV_RE_InstalledOp84
