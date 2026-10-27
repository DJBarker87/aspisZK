import RPt_FJc_WeightValues
import RPt_FIo_Constants
set_option autoImplicit false
noncomputable section
namespace AspisR1.FJc_WeightConstants
open FJc_WeightValues
open AspisR1CurrentWide.Proof FIo_FieldBridge

theorem zero : Canon FIn_WeightsExtract.field.QM31.ZERO ∧
    decode FIn_WeightsExtract.field.QM31.ZERO=0 := by
  constructor
  · simp [Canon,FIo_QMValues.Canon,FIo_CMValues.Canon,FIo_Install.toQ,FIn_WeightsExtract.field.QM31.ZERO]
  · apply QuadraticAlgebra.ext <;> apply QuadraticAlgebra.ext <;>
      simp [decode,decodeQM,AspisR1.ExtractedCurrentQM31Exact.decode,toQM,toCM,decodeC,decodeM,qm,cm,FIo_Install.toQ,FIn_WeightsExtract.field.QM31.ZERO] <;> rfl

theorem one : Canon FIn_WeightsExtract.field.QM31.ONE ∧
    decode FIn_WeightsExtract.field.QM31.ONE=1 := by
  constructor
  · simp [Canon,FIo_QMValues.Canon,FIo_CMValues.Canon,FIo_Install.toQ,FIn_WeightsExtract.field.QM31.ONE]
  · apply QuadraticAlgebra.ext <;> apply QuadraticAlgebra.ext <;>
      simp [decode,decodeQM,AspisR1.ExtractedCurrentQM31Exact.decode,toQM,toCM,decodeC,decodeM,qm,cm,FIo_Install.toQ,FIn_WeightsExtract.field.QM31.ONE] <;> rfl
#print axioms zero
#print axioms one
end AspisR1.FJc_WeightConstants
end
