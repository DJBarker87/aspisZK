import NEL_CopyArrayLaw
set_option autoImplicit false
noncomputable section
namespace NEL_OrderedWrites
open Aeneas Aeneas.Std Result

/-- The second child consumes the actual first child's updated allocation.
Both sources may differ, and overlap is permitted; execution order is retained. -/
theorem two_windows {N W V : Usize} (dst : Array U8 N)
    (first : Array U8 W) (second : Array U8 V) (a b k : Nat)
    (fit_first : a + W.val ≤ N.val) (fit_second : b + V.val ≤ N.val) :
    KMX_CopyMeaning.loop (fun j => second.val[j-b]?)
      (fun j => KMX_CopyMeaning.loop (fun i => first.val[i-a]?)
        (fun i => dst.val[i]?) a W.val j) b V.val k =
      ((dst.setSlice! a first.val).setSlice! b second.val).val[k]? := by
  have same_prestate :
      (fun j => KMX_CopyMeaning.loop (fun i => first.val[i-a]?)
        (fun i => dst.val[i]?) a W.val j) =
      (fun j => (dst.setSlice! a first.val).val[j]?) := by
    funext j
    exact NEL_CopyArrayLaw.loop_binding dst first a j fit_first
  rw [same_prestate]
  exact NEL_CopyArrayLaw.loop_binding (dst.setSlice! a first.val) second b k fit_second

#print axioms two_windows
end NEL_OrderedWrites
