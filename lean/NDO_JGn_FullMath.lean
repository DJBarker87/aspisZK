import NDO_JGn_FullEven
import NDO_JGn_FullOdd
import NDO_JGn_FullPow0
import NDO_JGn_FullMid
import NDO_JGn_FullPow1
import NDO_JGn_FullFinal
set_option autoImplicit false
noncomputable section
namespace AspisR1.JGn_FullMath
open FIw_ArrayValue (decoded)
theorem value : R0P.poseidonInterpolatedFullPair (decoded JGl_NumericData.a)
    (decoded JGl_NumericData.low)=decoded JGl_VectorData.full := by
  have first : R0P.poseidonFullRound (decoded JGl_NumericData.a)
      (FJe_FullConstants.even JGl_NumericData.low)=decoded JGn_FullPhaseData.mid := by
    unfold R0P.poseidonFullRound
    rw [JGn_FullEven.value,JGn_FullPow0.value,JGn_FullMid.value]
  have second : R0P.poseidonFullRound (decoded JGn_FullPhaseData.mid)
      (FJe_FullConstants.odd JGl_NumericData.low)=decoded JGl_VectorData.full := by
    unfold R0P.poseidonFullRound
    rw [JGn_FullOdd.value,JGn_FullPow1.value,JGn_FullFinal.value]
  exact (congrArg (fun state : Fin 16→FIv_NativeValue.K =>
    R0P.poseidonFullRound state (FJe_FullConstants.odd JGl_NumericData.low)) first).trans second
#print axioms value
end AspisR1.JGn_FullMath
end
