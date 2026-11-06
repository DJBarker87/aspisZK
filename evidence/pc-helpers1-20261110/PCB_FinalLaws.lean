import PCB_FinalRef.Funs
set_option autoImplicit false
open Aeneas Aeneas.Std Result
namespace PCB_FinalLaws
-- Reviewed runtime boundary transcription: the deployed body calls
-- set_return_data(&[]) and returns its unit reply. No value trust added.
def clearStep {S R : Type} (setReturnData : List U8 → S → R) (state : S) : R :=
  setReturnData [] state

theorem clear {S R : Type} (setReturnData : List U8 → S → R) (state : S) :
    clearStep setReturnData state = setReturnData [] state ∧
    PCB_FinalRef.clear_ref = ok () := by constructor <;> rfl

theorem preparation {P : Type} (x : PCB_FinalRef.Plan P) :
    PCB_FinalRef.preparation_ref x = ok x.preparation := by rfl

#print axioms clear
#print axioms preparation
end PCB_FinalLaws
