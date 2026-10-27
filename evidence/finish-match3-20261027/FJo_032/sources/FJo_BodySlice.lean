import SdkD_WriterCells
set_option autoImplicit false
noncomputable section
namespace AspisR1.FJo_BodySlice
open Aeneas Aeneas.Std Result
open OraclePortCompactDraft MultiproofConeCanonical
open AspisV8R19.DuplexFrames AspisV8R19.SqueezeOracleBridge
/-- A symbolic 32-byte slice of the actual sparse writer selector. -/
theorem value (p : CheckpointBytes5Writer.Prepared) (a : CheckpointBytes5Writer.Accumulator)
    (hp hu : Array U8 32#usize) (offset : Nat) (room : offset+32≤1736)
    (bytes : Bytes) (len : bytes.length=32)
    (cells : ∀ i : Fin 32, ∃ v,
      OraclePortCkptAbi2Extracted.body_byte p a hp hu (Usize.ofNat (offset+i.val) (by scalar_tac))=ok v ∧
      bytes[i.val]?=some (decodeByte v)) :
    slice (CheckpointBytesDecodeC5.sourceBody p a hp hu) offset 32=bytes := by
  apply List.ext_getElem
  · simp only [slice,List.length_take,List.length_drop,CheckpointBytesDecodeC5.sourceBody,List.length_ofFn,len]
    omega
  · intro i hi hj
    have bound : i<32 := by simpa only [len] using hj
    obtain ⟨v,call,byte⟩ := cells ⟨i,bound⟩
    have cell := SdkD_WriterCells.selector p a hp hu (offset+i) (by omega) v call
    have left : (slice (CheckpointBytesDecodeC5.sourceBody p a hp hu) offset 32)[i]?=
        (CheckpointBytesDecodeC5.sourceBody p a hp hu)[offset+i]? := by
      simp only [slice,List.getElem?_take,bound,ite_true,List.getElem?_drop]
    rw [←left,List.getElem?_eq_getElem hi] at cell
    rw [List.getElem?_eq_getElem hj] at byte
    exact Option.some.inj (cell.trans byte.symm)
#print axioms value
end AspisR1.FJo_BodySlice
end
