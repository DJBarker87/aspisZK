import FIw_PackTotal
set_option autoImplicit false
noncomputable section
namespace AspisR1.FIw_PackNonvacuity
open Aeneas Aeneas.Std Result FIq_Native
open FIv_NativeArithmetic (NQ qm)
open FIv_NativeValue (Canon decode)

def zero : Array NQ 4#usize := Array.repeat 4#usize field.QM31.ZERO

theorem value : ∃ out,field.qm31_pack_base4 (Array.to_slice zero)=ok out ∧
    Canon out ∧ decode out=0 := by
  have all : ∀ x∈zero.val,Canon x := by
    intro x hx
    have eq : x=field.QM31.ZERO := List.eq_of_mem_replicate hx
    exact eq ▸ FIv_NativeValue.zero.1
  have len : (Array.to_slice zero).length=4 := zero.property
  obtain ⟨out,success,canon⟩ := FIw_PackTotal.source (Array.to_slice zero) len all
  obtain ⟨copied,same,_,v⟩ := FIw_PackSource.value (Array.to_slice zero) out len all success
  refine ⟨out,success,canon,?_⟩
  have inputs : (fun j : Fin 4=>qm (FIw_ArrayValue.cells copied j))=
      (fun _ : Fin 4=>qm field.QM31.ZERO) := by
    funext j
    unfold FIw_ArrayValue.cells
    rw [same]
    simp only [Array.to_slice,zero,Array.repeat,List.getElem_replicate]
  rw [v,inputs]
  have z := FIv_NativeValue.zero.2
  simp only [ExtractedMaskQmPackBase4Arithmetic.mathematicalPack,z,mul_zero,add_zero]
#print axioms value
end AspisR1.FIw_PackNonvacuity
end
