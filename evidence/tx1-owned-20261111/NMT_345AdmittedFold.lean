import NMT_345SelectedFold
import NMT_345SelectCongr
import NMT_345SplitSelect
set_option autoImplicit false
noncomputable section
namespace NMT_345
open Aeneas Aeneas.Std Result

def admittedFold {W : Type} (c : Calls) (s : Parent W) : Result Ret :=
 if Slice.len s.accounts != 3#usize then .ok (.Err .InvalidInstructionData)
 else select s (selectedFold c)

theorem admitted_fold {W : Type} (c : Calls) (s : Parent W) :
 admitted c s = admittedFold c s := by
 rw [admitted_select]
 unfold admittedFold
 split
 · rfl
 · exact select_congr s _ _ (selected_fold c)
#print axioms admitted_fold
end NMT_345
