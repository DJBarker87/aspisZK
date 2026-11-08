import NNT_Root241
import NNS_Field
set_option autoImplicit false
noncomputable section
namespace NNT_Field
open RSL RSL.TX2_241 RSL.NNT NNS_Fold241
abbrev install := @NNS_Field.install

def Required (ch : NMX_R4_Authentication.Choices) : Prop :=
 ∀ (R0 : Bytes → Bytes → Prop) (w : Bytes → Bytes → Bytes → Spec (Except V0.VErr Unit)),
 LawRefines V0 R0 w → TX2_242.RowSpec_242 L D (NMX_R6_Validation.validate ch) →
 RowSpec_241 L D (TAS.lib V0 R0 w) (NMX_R9_StageTwo.stage2 ch)

theorem r241 (ch : NMX_R4_Authentication.Choices) : Required ch :=
 NNT_Root241.parametric ch

example {VL : VLib} (I0 : TAS.Impl L V0 VL) (ch : NMX_R4_Authentication.Choices) :
 Required ch =
 (∀ (R0 : Bytes → Bytes → Prop) (w : Bytes → Bytes → Bytes → Spec (Except V0.VErr Unit)),
 LawRefines V0 R0 w → TX2_242.RowSpec_242 L D (install I0 ch).f242 →
 RowSpec_241 L D (TAS.lib V0 R0 w) (install I0 ch).f241) := rfl

example {VL : VLib} (I0 : TAS.Impl L V0 VL) (ch : NMX_R4_Authentication.Choices)
 (roots : NMS_RootsL L D V0 VL (install I0 ch)) : Required ch := roots.r241
#print axioms r241
end NNT_Field
