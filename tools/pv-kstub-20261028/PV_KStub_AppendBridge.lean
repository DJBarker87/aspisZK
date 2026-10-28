import PV_KStub_AppendCoordinates
import PV_KStub_OptionCoordinates
namespace PV_KStub_AppendBridge
/-- In-range prefix/tail laws and exact length give complete optional coordinates. -/
theorem complete_append {α : Type} (actual prefix tail : Nat → α) (n m : Nat)
    (head : ∀ k, k<n → actual k=prefix k)
    (suffix : ∀ j, j<m → actual (n+j)=tail j) :
    ∀ k, PV_KStub_OptionCoordinates.view actual (n+m) k =
      PV_KStub_OptionCoordinates.view
        (PV_KStub_AppendCoordinates.appended prefix tail n) (n+m) k := by
  apply PV_KStub_OptionCoordinates.complete_view
  intro k hk
  by_cases h : k<n
  · rw [PV_KStub_AppendCoordinates.prefix_frame prefix tail n k h]
    exact head k h
  · have hj : k-n<m := by omega
    have he : n+(k-n)=k := by omega
    have hs := suffix (k-n) hj
    rw [he] at hs
    simpa only [PV_KStub_AppendCoordinates.appended, if_neg h] using hs
#print axioms complete_append
end PV_KStub_AppendBridge
