import NMP_PrepareSource
set_option autoImplicit false
noncomputable section
namespace AspisR1.NMP_PrepareAllocationError
open Aeneas Aeneas.Std Result NMP_prepare NMP_Emitted NMP_PrepareSteps
open NMT_CallTree (run Event)
/-- A returned Rust allocation error keeps g; it is distinct from outer abort. -/
theorem stopped_prefix {H W : Type} (c : Calls) (s : Parent H W) (e : aspis_core.r0.Error)
 (h : c.c1 core.marker.CopyU8 14759#usize 0#u8 = .ok (.Err e)) :
 run (body c s) = (.ok (.Err verifier.Error.Allocation,s.scratch),
  [Event.call "TX1:064/filled" (14759#usize,0#u8)
   (.ok (.Err e : core.result.Result (alloc.vec.Vec U8) aspis_core.r0.Error))]) := by
 unfold body
 rw [execute]
 simp only [step]
 rw [h]
 rfl
#print axioms stopped_prefix
end AspisR1.NMP_PrepareAllocationError
