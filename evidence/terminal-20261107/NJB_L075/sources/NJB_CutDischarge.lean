import NJB_Cuts
import NJB_ActiveRawHigh
import NJB_MaskTable
set_option autoImplicit false
noncomputable section
namespace AspisR1.NJB_CutDischarge
open Aeneas Aeneas.Std Result
open FIv_NativeArithmetic (NQ)
open FIv_NativeValue (Canon decode)
/-- The high native cut's complete write frame is instantiated at the actual
emitted add Result. The child-call equation is a conclusion, never a premise. -/
theorem high (source : Fin 64 → NQ) (before : Fin 7 → NQ) (b : Fin 64)
 (hh : ∀ i,Canon (source i)) (hs : ∀ i,Canon (before i)) :
 ∃ reply,FIq_Native.field.QM31.add (before (NJB_ActiveModel.key b)) (source b)=ok reply ∧
 Canon reply ∧ ∀ after event calls next,
 NJB_Cuts.high source before after b reply event calls next →
 NJB_ActiveRawHigh.step source before b=ok after := by
 obtain ⟨reply,call,hr,_⟩ := NJB_StubLaws.qm_add (before (NJB_ActiveModel.key b)) (source b) (hs _) (hh _)
 refine ⟨reply,call,hr,?_⟩
 intro after event calls next cut
 have key : R0P.activeMaskCoordinate (NJB_MaskTable.nativeMasks b)=NJB_ActiveModel.key b := by
  rw [NJB_MaskTable.source_eq_model];rfl
 have frame := cut.2.2.2.2.2.2.2.2
 have same : after=(fun i=>if NJB_ActiveModel.key b=i then reply else before i) := by
  funext i
  simpa only [key] using frame i
 rw [same]
 simp only [NJB_ActiveRawHigh.step,call,bind_tc_ok]
#print high
#print axioms high
end AspisR1.NJB_CutDischarge
end
