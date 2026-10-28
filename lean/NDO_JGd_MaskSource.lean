import NDO_JGd_MaskValue
import NDO_JGd_MainInjective
set_option autoImplicit false
noncomputable section
namespace AspisR1.JGd_MaskSource
open Aeneas Aeneas.Std Result FIp_SemanticArithmetic FIp_SemanticValues

theorem source : FIp_SemanticArithmetic.mask JFu_MaskInputs.c1 JFu_MaskInputs.maskOnly
    JFu_MaskInputs.g JFu_MaskInputs.point = ok JGd_NumericData.mask := by
  obtain ⟨out,call,hc,hv⟩ := JGd_MaskModel.source
    JFu_MaskInputs.c1 JFu_MaskInputs.maskOnly JFu_MaskInputs.point JFu_MaskInputs.g
    JFu_MaskInputs.c1_canonical JFu_MaskInputs.maskOnly_canonical
    JFu_MaskInputs.point_canonical JFu_MaskInputs.g_canonical
  have same := JGd_MainInjective.source out JGd_NumericData.mask hc
    JGd_NumericData.mask_canonical (hv.trans JGd_MaskValue.source)
  exact same ▸ call
#print axioms source
end AspisR1.JGd_MaskSource
end
