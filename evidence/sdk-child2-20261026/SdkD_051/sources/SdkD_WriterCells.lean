import SdkD_FirstPaths
import CheckpointBytesSparseDigest
set_option autoImplicit false
noncomputable section
namespace AspisR1.SdkD_WriterCells
open Aeneas Aeneas.Std Result
open AspisV8R19.DuplexFrames AspisV8R19.SourceDuplexStep AspisV8R19.SqueezeOracleBridge
open CheckpointBytesDecodeC5 MultiproofConeCanonical

theorem selector (p : CheckpointBytes5Writer.Prepared) (a : CheckpointBytes5Writer.Accumulator)
    (hp hu : Array U8 32#usize) (i : Nat) (bound : i < 1736) (value : U8)
    (source : OraclePortCkptAbi2Extracted.body_byte p a hp hu (Usize.ofNat i (by scalar_tac)) = ok value) :
    (sourceBody p a hp hu)[i]? = some (decodeByte value) := by
  simp only [sourceBody,List.getElem?_ofFn,bound,↓reduceDIte,source]

theorem root0 (p : CheckpointBytes5Writer.Prepared) (a : CheckpointBytes5Writer.Accumulator)
    (hp hu : Array U8 32#usize) :
    OraclePortCompactDraft.slice (sourceBody p a hp hu) 112 32 =
      bytesOf (p.roots.val[0]'(by simp [p.roots.property])).val := by
  apply List.ext_getElem
  · simp only [OraclePortCompactDraft.slice,List.length_take,List.length_drop,sourceBody,
      List.length_ofFn,bytesOf,List.length_map,(p.roots.val[0]'(by simp [p.roots.property])).property]
    rfl
  · intro i hi hj
    have bound : i < 32 := by simpa [bytesOf] using hj
    have cell := selector p a hp hu (112+i) (by omega)
      ((p.roots.val[0]'(by simp [p.roots.property])).val[i]'(by
        simpa using bound))
      (CheckpointBytesSparseDigest.root0_dispatch p a hp hu
        (Usize.ofNat i (by scalar_tac)) (by simpa using bound))
    have left : (OraclePortCompactDraft.slice (sourceBody p a hp hu) 112 32)[i]? =
        (sourceBody p a hp hu)[112+i]? := by
      simp only [OraclePortCompactDraft.slice,List.getElem?_take,bound,ite_true,List.getElem?_drop]
    rw [List.getElem?_eq_getElem hi] at left
    rw [← left] at cell
    have right : (bytesOf (p.roots.val[0]'(by simp [p.roots.property])).val)[i]? =
      some (decodeByte ((p.roots.val[0]'(by simp [p.roots.property])).val[i]'(by
        simpa using bound))) := by
      simp only [bytesOf,List.getElem?_map,List.getElem?_eq_getElem (by
        simpa using bound),Option.map_some]
    rw [List.getElem?_eq_getElem hj] at right
    exact Option.some.inj (cell.trans right.symm)

#print axioms selector
#print axioms root0
end AspisR1.SdkD_WriterCells
end
