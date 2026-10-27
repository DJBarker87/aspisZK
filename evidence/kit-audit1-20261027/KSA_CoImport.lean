import KSA_XRn_Join_Funs
import LPn_DotClosed
open Aeneas Aeneas.Std Result
set_option autoImplicit false
namespace KSA

def windowsToLP {T : Type} (s : KSA_Isolated.core.slice.iter.Windows T) :
    core.slice.iter.Windows T := ⟨s.slice,s.width,s.index⟩
def windowsFromLP {T : Type} (s : core.slice.iter.Windows T) :
    KSA_Isolated.core.slice.iter.Windows T := ⟨s.slice,s.width,s.index⟩
theorem windows_roundtrip {T : Type} (s : KSA_Isolated.core.slice.iter.Windows T) :
    windowsFromLP (windowsToLP s) = s := by cases s; rfl

theorem windows_next {T : Type} (s : KSA_Isolated.core.slice.iter.Windows T) :
    KSA_Isolated.core.slice.iter.Windows.Insts.CoreIterTraitsIteratorIteratorSharedASlice.next s =
    (do
      let (v,t) ← core.slice.iter.Windows.Insts.CoreIterTraitsIteratorIteratorSharedASlice.next (windowsToLP s)
      ok (v,windowsFromLP t)) := by
  cases s with
  | mk slice width index =>
    unfold KSA_Isolated.core.slice.iter.Windows.Insts.CoreIterTraitsIteratorIteratorSharedASlice.next
      core.slice.iter.Windows.Insts.CoreIterTraitsIteratorIteratorSharedASlice.next
      windowsToLP windowsFromLP
    split <;> rfl
#print axioms windows_roundtrip
#print axioms windows_next
#print axioms LPn.Dot.native_result
#print axioms LPn.Claims.total
#print axioms LPn.Decode.native_success
#print axioms LPn.Expand.native_result
end KSA
