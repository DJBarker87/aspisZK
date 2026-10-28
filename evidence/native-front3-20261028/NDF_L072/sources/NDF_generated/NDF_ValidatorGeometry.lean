import NDF_ChunkGeometry
import NDF_ValidatorWindows
set_option autoImplicit false
namespace NDF_ValidatorGeometry
open Aeneas Aeneas.Std Result

theorem decomposition (bytes : Slice U8) :
    ∃ ce, core.slice.Slice.chunks_exact bytes 32#usize=ok ce ∧
      ce.chunks=NDF_ValidatorWindows.windows bytes (bytes.val.length/32) 0 ∧
      ∀ chunk∈ce.chunks,chunk.val.length=32 := by
  unfold core.slice.Slice.chunks_exact
  simp only [show (32#usize).val=32 by scalar_tac,show 0<32 by decide,dif_pos]
  refine ⟨_,rfl,?_,?_⟩
  · apply List.ext_getElem
    · simp only [List.length_map,List.length_attach,NDF_ValidatorWindows.windows,
        List.length_range',Nat.sub_zero,NDF_ChunkGeometry.count]
    · intro i hi hj
      apply Subtype.ext
      have bound : i<bytes.val.length/32 := by
        simpa only [List.length_map,List.length_attach,NDF_ChunkGeometry.count] using hi
      have selected := NDF_ChunkGeometry.window bytes.val i bound
      have rawBound : i<(List.toChunksExact 32 (by decide) bytes.val).1.length := by
        rw [NDF_ChunkGeometry.count]
        exact bound
      rw [List.getElem?_eq_getElem rawBound] at selected
      have raw := Option.some.inj selected
      simpa only [List.getElem_map,List.getElem_attach,NDF_ValidatorWindows.windows,
        List.getElem_range',Nat.zero_add,NDF_ValidatorWindows.window] using raw
  · intro chunk member
    obtain ⟨raw,_,rfl⟩ := List.mem_map.mp member
    exact NDF_ChunkGeometry.widths 32 (by decide) bytes.val raw.val raw.property

#print axioms decomposition
end NDF_ValidatorGeometry
