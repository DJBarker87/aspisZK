import RPz7_SdkD_WriterCells
set_option autoImplicit false
noncomputable section
namespace AspisR1.SdkD_WriterRoot1
open Aeneas Aeneas.Std Result
open AspisV8R19.DuplexFrames AspisV8R19.SourceDuplexStep AspisV8R19.SqueezeOracleBridge
open CheckpointBytesDecodeC5 MultiproofConeCanonical SdkD_WriterCells
theorem root1 (p : CheckpointBytes5Writer.Prepared) (a : CheckpointBytes5Writer.Accumulator)
    (hp hu : Array U8 32#usize) :
    OraclePortCompactDraft.slice (sourceBody p a hp hu) 144 32 =
      bytesOf (p.roots.val[1]'(by simp [p.roots.property])).val := by
  apply List.ext_getElem
  · simp only [OraclePortCompactDraft.slice,List.length_take,List.length_drop,sourceBody,
      List.length_ofFn,bytesOf,List.length_map,(p.roots.val[1]'(by simp [p.roots.property])).property]
    rfl
  · intro i hi hj
    have bound : i < 32 := by simpa [bytesOf] using hj
    have cell := selector p a hp hu (144+i) (by omega)
      ((p.roots.val[1]'(by simp [p.roots.property])).val[i]'(by
        simpa using bound))
      (CheckpointBytesSparseDigest.root1_dispatch p a hp hu
        (Usize.ofNat i (by scalar_tac)) (by simpa using bound))
    have left : (OraclePortCompactDraft.slice (sourceBody p a hp hu) 144 32)[i]? =
        (sourceBody p a hp hu)[144+i]? := by
      simp only [OraclePortCompactDraft.slice,List.getElem?_take,bound,ite_true,List.getElem?_drop]
    rw [List.getElem?_eq_getElem hi] at left
    rw [← left] at cell
    have right : (bytesOf (p.roots.val[1]'(by simp [p.roots.property])).val)[i]? =
      some (decodeByte ((p.roots.val[1]'(by simp [p.roots.property])).val[i]'(by
        simpa using bound))) := by
      simp only [bytesOf,List.getElem?_map,List.getElem?_eq_getElem (show i < (p.roots.val[1]'(by simp [p.roots.property])).val.length from by simpa using bound),Option.map_some]
    rw [List.getElem?_eq_getElem hj] at right
    exact Option.some.inj (cell.trans right.symm)

#print axioms root1
end AspisR1.SdkD_WriterRoot1
end
