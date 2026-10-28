import NCD_FillFrame
import NCD_B_NCB_Filled14759
set_option autoImplicit false
namespace NCD_FillAssociation
open Aeneas Aeneas.Std Result AspisR1 AspisR1ClaimsUnrolledParent AspisR1.NP6_StdModel
/-- Read the initialized prefix of the SAME full carrier. The exterior frame
and allocation metadata remain available from NCD_FillFrame; no owned vector
or native trace existence follows from the readback relation alone. -/
theorem contents {α : Type} {value : α} {s out : NCD_FillFrame.Carrier α} {n : Nat}
    (empty : s.length=0) (trace : NCD_FillFrame.Trace value s n out)
    (cells : List α) (length : cells.length=n)
    (readback : ∀ i (bound : i<cells.length), cells[i]=out.storage (s.address+i)) :
    cells=List.replicate n value := by
  apply List.ext_getElem
  · simp only [List.length_replicate,length]
  · intro i hi hj
    have inside : s.address+s.length≤s.address+i ∧ s.address+i<s.address+s.length+n := by omega
    have initialized := NCD_FillFrame.storage trace (s.address+i)
    rw [if_pos inside] at initialized
    rw [readback i hi,initialized]
    simp

/-- Associate that native readback with the inherited exact preparation-size
model result; no new initialization theorem or allocation success is assumed. -/
theorem model14759 {T : Type} (copy : core.marker.Copy T) (value : T)
    (cloned : copy.cloneInst.clone value=ok value)
    (s out : NCD_FillFrame.Carrier T) (empty : s.length=0)
    (trace : NCD_FillFrame.Trace value s 14759 out) (cells : List T)
    (length : cells.length=14759)
    (readback : ∀ i (bound : i<cells.length), cells[i]=out.storage (s.address+i)) :
    ∃ model : alloc.vec.Vec T,
      aspis_core.r0.heap.filled (ClaimsUnrolledFinish.external (calls (.Ok ())))
        copy 14759#usize value=ok (.Ok model) ∧ model.val=cells := by
  have same := contents empty trace cells length readback
  refine ⟨⟨List.replicate 14759 value,by simp only [List.length_replicate];scalar_tac⟩,
    NCB_Filled14759.model copy value cloned,same.symm⟩
#print axioms contents
#print axioms model14759
end NCD_FillAssociation
