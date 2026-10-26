import RPz7_SdkD_WriterCells
import CheckpointBytesQuery
set_option autoImplicit false
noncomputable section
namespace AspisR1.SdkD_WriterQueryCells
open Aeneas Aeneas.Std Result
open AspisV8R19.DuplexFrames AspisV8R19.SourceDuplexStep AspisV8R19.SqueezeOracleBridge
open CheckpointBytesDecodeC5 MultiproofConeCanonical OraclePortCompactDraft

theorem query (p : CheckpointBytes5Writer.Prepared) (a : CheckpointBytes5Writer.Accumulator)
    (hp hu : Array U8 32#usize) (j : Fin 22) :
    slice (sourceBody p a hp hu) (320+4*j.val) 4 =
      le32 (p.queries.val[j.val]'(by simpa using j.isLt)).val := by
  apply List.ext_getElem
  · simp only [slice,List.length_take,List.length_drop,sourceBody,List.length_ofFn,
      le32,List.length_map,List.length_range]
    have := j.isLt
    omega
  · intro i hi hj
    have bound : i < 4 := by simpa [le32] using hj
    obtain ⟨value,source,encoded⟩ := CheckpointBytesQuery.query_bytes p a hp hu j
      (Usize.ofNat i (by scalar_tac)) (by simpa using bound)
    have cell := SdkD_WriterCells.selector p a hp hu (320+4*j.val+i)
      (by have := j.isLt; omega) value source
    have left : (slice (sourceBody p a hp hu) (320+4*j.val) 4)[i]? =
      (sourceBody p a hp hu)[320+4*j.val+i]? := by
      simp only [slice,List.getElem?_take,bound,ite_true,List.getElem?_drop]
    rw [List.getElem?_eq_getElem hi] at left
    rw [←left] at cell
    have encoded' : (le32 (p.queries.val[j.val]'(by simpa using j.isLt)).val)[i]? =
      some (decodeByte value) := by simpa using encoded
    rw [List.getElem?_eq_getElem hj] at encoded'
    exact Option.some.inj (cell.trans encoded'.symm)

#print axioms query
end AspisR1.SdkD_WriterQueryCells
end
