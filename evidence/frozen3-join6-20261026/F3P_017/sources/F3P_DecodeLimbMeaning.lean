import F3L_RhoMeaning
import ActualDecodeKStrictQM31Parser
import PAln_LowRead
set_option autoImplicit false
noncomputable section
namespace AspisR1.F3P_DecodeLimbMeaning
open RetainedFieldByteCodec

theorem numeric (xs : QM31Limbs) :
    F3L_RhoMeaning.decode (AspisS1ExtractedRoundChildren.decoderQMToMain
      (ActualDecodeKStrictQM31Parser.limbsToActual xs))=RetainedExactLimbCodec.qm31ExactLimbEquiv xs := by
  have limb (x : M31Value) :
      (x.val : AspisV8R15.ExactTowerBase.M31Exact)=RetainedExactLimbCodec.m31ResidueEquiv x := by
    apply ZMod.val_injective AspisV8R15.ExactTowerBase.P
    change (x.val : ZMod AspisV8R15.ExactTowerBase.P).val=x.val
    exact ZMod.val_natCast_of_lt x.isLt
  apply QuadraticAlgebra.ext
  · apply QuadraticAlgebra.ext
    · exact limb (xs 0)
    · exact limb (xs 1)
  · apply QuadraticAlgebra.ext
    · exact limb (xs 2)
    · exact limb (xs 3)

#print axioms numeric
end AspisR1.F3P_DecodeLimbMeaning
end
