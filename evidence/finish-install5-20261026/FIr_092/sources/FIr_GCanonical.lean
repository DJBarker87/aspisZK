import FIr_CompositionColumns
import FIr_SelectedClaim
set_option autoImplicit false
noncomputable section
namespace AspisR1.FIr_GCanonical
open Aeneas Aeneas.Std Result
open FIr_TerminalTrace
open FIr_NativeValue (Canon)

theorem canonical (pub : SemPub) (claims : Array NQ 84#usize) (point : Array NQ 10#usize)
    (lambda chi theta comp g h active : NQ) (c1 : Array NQ 16#usize) (mask : Array NQ 10#usize)
    (success : composition pub claims point lambda chi theta=ok (.Ok (comp,c1,mask,g,h,active)))
    (all : ∀ x∈claims.val,Canon x) : Canon g := by
  obtain ⟨_,column,selected,called⟩ := FIr_CompositionColumns.reached pub claims point lambda chi theta comp g h active c1 mask success
  exact FIr_SelectedClaim.canonical claims 0#usize column g all called

#print axioms canonical
end AspisR1.FIr_GCanonical
end
