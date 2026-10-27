import F3P_LowDecodeInjective
import F3P_CircleCell
set_option autoImplicit false
noncomputable section
namespace AspisR1.F3P_LowCellRead
open AspisV8R19.DuplexFrames

theorem identify (bytes : Bytes) (a b : SemanticCoefficientCodec.LowWide)
    (full : SemanticCoefficientCodec.decodeLow bytes=some a)
    (low : SemanticCoefficientCodec.decodeLow (bytes.take 16++List.replicate 16 0)=some b) :
    a=b := by
  apply F3P_LowDecodeInjective.low_bytes
  rw [SemanticCoefficientCodec.encodeLow_of_decode bytes a full,
    SemanticCoefficientCodec.encodeLow_of_decode _ b low]
  have length := congrArg List.length (SemanticCoefficientCodec.encodeLow_of_decode bytes a full)
  rw [SemanticCoefficientCodec.encodeLow_length] at length
  have enough : (bytes.take 16).length=16 := by simp only [List.length_take];omega
  rw [List.take_append,List.take_of_length_le (by omega),enough,Nat.sub_self,List.take_zero,List.append_nil]

#print axioms identify
end AspisR1.F3P_LowCellRead
end
