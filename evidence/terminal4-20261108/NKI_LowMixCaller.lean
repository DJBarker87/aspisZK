import NKI_LowMixFold
import NKI_PublicDomains
set_option autoImplicit false
noncomputable section
namespace AspisR1.NKI_LowMixCaller
open Aeneas Aeneas.Std Result
open FIv_NativeValue (Canon decode)
open NKI_LowMix (State)
open NKI_PublicDomains (Selectors)
def low (s : Selectors) (g : Fin 3) := NJB_ArrayCarrier.cell s.low (NKI_PublicDomains.lows g)
def zero : State := fun _=>FIq_Native.field.QM31.ZERO
/--251concrete low0/11/12three-block suffix from ZERO2. This is SUPPORT,
not the missing complete public-digest parent/cohort association. -/
theorem source (s : Selectors) (sums : Fin 3 → State) (hl : FIw_ArrayValue.canonical s.low)
 (hs : ∀ g j,Canon (sums g j)) :
 ∃ out,NKI_LowMixFold.run (low s) sums (List.finRange 3) zero=ok out ∧ (∀ j,Canon (out j)) ∧
 ∀ j,decode (out j)=((List.finRange 3).map (fun g=>decode (low s g)*decode (sums g j))).sum := by
 obtain ⟨out,co,ho,vo⟩ := NKI_LowMixFold.source (low s) sums (fun _=>NJB_ArrayCarrier.canonical_cell s.low hl _) hs (List.finRange 3) zero (fun _=>FIv_NativeValue.zero.1)
 exact ⟨out,co,ho,fun j=>by simpa only [zero,FIv_NativeValue.zero.2,zero_add] using vo j⟩
#print axioms source
end AspisR1.NKI_LowMixCaller
end
