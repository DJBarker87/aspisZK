import NMF_WriterRoots
set_option autoImplicit false
noncomputable section
namespace NNC_WriterCells
open Aeneas Aeneas.Std Result AspisR1
open AspisV8R19.DuplexFrames AspisV8R19.SourceDuplexStep AspisV8R19.SqueezeOracleBridge
open CheckpointBytesDecodeC5 MultiproofConeCanonical
/- The arbitrary-offset generic block shape was retired after L022/L023.
These fixed sparse selectors reuse SdkD_WriterCells.selector directly. -/
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
#print axioms proofHash
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
#print axioms publicHash
end NNC_WriterCells
