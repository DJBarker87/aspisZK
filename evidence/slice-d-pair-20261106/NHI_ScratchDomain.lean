import NHI_FilledModel
import NHI_Tensor
set_option autoImplicit false
namespace NHI_ScratchDomain
open Aeneas Aeneas.Std Result AspisR1 LPi_FieldValues NP6_StdModel
abbrev zero := FIo_Native.aspis_core.field.QM31.ZERO

theorem zero_canonical : canonQ zero := by
 unfold zero FIo_Native.aspis_core.field.QM31.ZERO
 simp only [canonQ,canonC,LPi_CMProduct.Canon]
 decide

/-- The exact initialized scratch vector is a tensor input on every returning
allocation. The reserve-error arm remains a full error, not an availability premise. -/
theorem initialized (reservation : Reservation) :
 letI := FIo_Install.allocation reservation
 FIo_Native.aspis_core.r0.heap.filled FIo_Native.aspis_core.field.QM31.Insts.CoreMarkerCopy 64#usize zero=
 NHI_FilledModel.result reservation 64#usize zero := NHI_FilledModel.qm reservation 64#usize zero

theorem domain :
 (NHI_FilledModel.vector 64#usize zero).val.length=64 ∧
 NHI_CellCanon.slice (NHI_FilledModel.vector 64#usize zero).deref := by
 refine ⟨?_,?_⟩
 · rw [NHI_FilledModel.length] <;> rfl
 · exact NHI_FilledModel.canonical 64#usize zero zero_canonical

#print axioms zero_canonical
#print axioms initialized
#print axioms domain
end NHI_ScratchDomain
