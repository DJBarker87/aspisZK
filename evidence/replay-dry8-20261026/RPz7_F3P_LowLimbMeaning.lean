import RPz7_F3P_DecodeLimbMeaning
set_option autoImplicit false
noncomputable section
namespace AspisR1.F3P_LowLimbMeaning
open RetainedFieldByteCodec

theorem embed (xs : QM31Limbs) :
    LiteralOpeningView.eK (RetainedExactLimbCodec.qm31ExactLimbEquiv xs)=
      WideExactLimbCodec.pairExactEquiv (xs,PAln_LowRead.zeroLimbs) := by
  apply QuadraticAlgebra.ext
  · rfl
  · exact PAln_LowRead.exact_zero.symm

#print axioms embed
end AspisR1.F3P_LowLimbMeaning
end
