import NMT_345PrefixCongr
import NMT_345MiddleCongr
import NMT_345BoundsFold
set_option autoImplicit false
noncomputable section
namespace NMT_345
open Aeneas Aeneas.Std Result
/-- Exact emitted value/control fold, not a RowSpec or physical packet. Each
call boundary was checked independently; the full parent survives in its frame. -/
def selectedFold {W : Type} (c : Calls) (s : Selected W) : Result Ret :=
 prefixFold c s (fun decoded => middleFold c decoded (boundsFold c))

theorem selected_fold {W : Type} (c : Calls) (s : Selected W) :
 rawSelected c s = selectedFold c s := by
 rw [prefix_fold]
 apply prefix_congr
 intro decoded
 rw [middle_fold]
 exact middle_congr c decoded _ _ (bounds_fold c)
#print axioms selected_fold
end NMT_345
