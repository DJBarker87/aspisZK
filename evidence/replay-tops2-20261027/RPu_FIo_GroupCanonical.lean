import RPu_FIo_GroupCoefficients
import RPu_FIo_GroupContract
set_option autoImplicit false
noncomputable section
namespace AspisR1.FIo_GroupCanonical
open Aeneas Aeneas.Std Result
open FIo_FieldBridge (NE)

theorem zeros (N : Usize) : FIo_ArrayCanon.Holds
    (Array.repeat N FIo_Native.aspis_core.field.wide_exact.WideExact.ZERO) := by
  intro x hx
  simp only [Array.repeat,List.mem_replicate] at hx
  rcases hx with ⟨_,rfl⟩
  exact FIo_Constants.zero.1

/-- Successful shipped grouped contraction preserves canonicality. Its input
coefficients come from the same checked source reader, not an extra premise. -/
theorem canonical (f : Slice U8) (low : Array NE 16#usize) (result : NE)
    (hlow : FIo_ArrayCanon.Holds low)
    (run : FIo_Native.weights.s2_grouped_inactive_pair f low=ok result) :
    FIo_WideValues.Canon result := by
  unfold FIo_Native.weights.s2_grouped_inactive_pair at run
  obtain ⟨coefficients,hcoefficients,run⟩ := Port3_PushFrame.bind_success _ _ _ run
  have hc := FIo_GroupCoefficients.canonical f _ _ coefficients (zeros _) hcoefficients
  exact FIo_GroupContract.canonical low coefficients hlow hc _ _ result FIo_Constants.zero.1 run

#print axioms zeros
#print axioms canonical
end AspisR1.FIo_GroupCanonical
end
