import NMP_PrepareSource
set_option autoImplicit false
noncomputable section
namespace AspisR1.NMP_PrepareAllocationAbort
open Aeneas Aeneas.Std Result NMP_prepare NMP_Emitted NMP_PrepareSteps
open NMT_CallTree (run Event)
/-- No split, expansion, semantic call or final world is appended to an abort. -/
theorem prefix {H W : Type} (c : Calls) (s : Parent H W) (e : Error)
 (h : c.c1 core.marker.CopyU8 14759#usize 0#u8 = .fail e) :
 run (body c s) = (.fail e,[Event.call "TX1:064/filled" (14759#usize,0#u8)
  (.fail e : Result (core.result.Result (alloc.vec.Vec U8) aspis_core.r0.Error))]) := by
 unfold body
 rw [execute]
 simp only [step]
 rw [h]
 rfl
#print axioms prefix
end AspisR1.NMP_PrepareAllocationAbort
