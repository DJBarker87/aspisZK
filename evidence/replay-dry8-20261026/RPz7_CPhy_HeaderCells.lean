import RPz7_SdkD_WriterCells
import CheckpointBytesSparseDigest
set_option autoImplicit false
noncomputable section
namespace AspisR1.CPhy_HeaderCells
open Aeneas Aeneas.Std Result
open AspisV8R19.DuplexFrames AspisV8R19.SourceDuplexStep AspisV8R19.SqueezeOracleBridge
open CheckpointBytesDecodeC5 MultiproofConeCanonical

theorem selector (p : CheckpointBytes5Writer.Prepared) (a : CheckpointBytes5Writer.Accumulator)
    (hp hu : Array U8 32#usize) (i : Nat) (bound : i < 1736) (value : U8)
    (source : OraclePortCkptAbi2Extracted.body_byte p a hp hu (Usize.ofNat i (by scalar_tac)) = ok value) :
    (sourceBody p a hp hu)[i]? = some (decodeByte value) := by
  simp only [sourceBody,List.getElem?_ofFn,bound,↓reduceDIte,source]

theorem proofHash (p : CheckpointBytes5Writer.Prepared) (a : CheckpointBytes5Writer.Accumulator)
    (hp hu : Array U8 32#usize) :
    OraclePortCompactDraft.slice (sourceBody p a hp hu) 16 32 =
      bytesOf hp.val := by
  apply List.ext_getElem
  · simp only [OraclePortCompactDraft.slice,List.length_take,List.length_drop,sourceBody,
      List.length_ofFn,bytesOf,List.length_map,hp.property]
    rfl
  · intro i hi hj
    have bound : i < 32 := by simpa [bytesOf] using hj
    have cell := SdkD_WriterCells.selector p a hp hu (16+i) (by omega)
      (hp.val[i]'(by
        simpa using bound))
      (CheckpointBytesSparseDigest.proofHash_dispatch p a hp hu
        (Usize.ofNat i (by scalar_tac)) (by simpa using bound))
    have left : (OraclePortCompactDraft.slice (sourceBody p a hp hu) 16 32)[i]? =
        (sourceBody p a hp hu)[16+i]? := by
      simp only [OraclePortCompactDraft.slice,List.getElem?_take,bound,ite_true,List.getElem?_drop]
    rw [List.getElem?_eq_getElem hi] at left
    rw [← left] at cell
    have right : (bytesOf hp.val)[i]? =
      some (decodeByte (hp.val[i]'(by
        simpa using bound))) := by
      simp only [bytesOf,List.getElem?_map,List.getElem?_eq_getElem (show i < hp.val.length from by simpa using bound),Option.map_some]
    rw [List.getElem?_eq_getElem hj] at right
    exact Option.some.inj (cell.trans right.symm)

theorem publicHash (p : CheckpointBytes5Writer.Prepared) (a : CheckpointBytes5Writer.Accumulator)
    (hp hu : Array U8 32#usize) :
    OraclePortCompactDraft.slice (sourceBody p a hp hu) 48 32 =
      bytesOf hu.val := by
  apply List.ext_getElem
  · simp only [OraclePortCompactDraft.slice,List.length_take,List.length_drop,sourceBody,
      List.length_ofFn,bytesOf,List.length_map,hu.property]
    rfl
  · intro i hi hj
    have bound : i < 32 := by simpa [bytesOf] using hj
    have cell := SdkD_WriterCells.selector p a hp hu (48+i) (by omega)
      (hu.val[i]'(by
        simpa using bound))
      (CheckpointBytesSparseDigest.publicHash_dispatch p a hp hu
        (Usize.ofNat i (by scalar_tac)) (by simpa using bound))
    have left : (OraclePortCompactDraft.slice (sourceBody p a hp hu) 48 32)[i]? =
        (sourceBody p a hp hu)[48+i]? := by
      simp only [OraclePortCompactDraft.slice,List.getElem?_take,bound,ite_true,List.getElem?_drop]
    rw [List.getElem?_eq_getElem hi] at left
    rw [← left] at cell
    have right : (bytesOf hu.val)[i]? =
      some (decodeByte (hu.val[i]'(by
        simpa using bound))) := by
      simp only [bytesOf,List.getElem?_map,List.getElem?_eq_getElem (show i < hu.val.length from by simpa using bound),Option.map_some]
    rw [List.getElem?_eq_getElem hj] at right
    exact Option.some.inj (cell.trans right.symm)


#print axioms proofHash
#print axioms publicHash
end AspisR1.CPhy_HeaderCells
end
