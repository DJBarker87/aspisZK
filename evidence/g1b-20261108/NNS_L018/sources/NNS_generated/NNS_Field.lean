import NNS_SameConstant
import NNS_Fold241
set_option autoImplicit false
noncomputable section
namespace NNS_Field
open RSL RSL.TX2_241 NNS_Fold241

/-- Literal installed function fields, with all other fields retained as data.
No wrapper replaces the credited241 implementation. This is not NMS_Roots. -/
def install {VL : VLib} (I0 : TAS.Impl L V0 VL) (ch : NMX_R4_Authentication.Choices) :
 TAS.Impl L V0 VL :=
 {I0 with f064 := AspisR1.NNH_064Install.f064,
  f241 := NMX_R9_StageTwo.stage2 ch, f242 := NMX_R6_Validation.validate ch}

/-- The still-missing field. A type declaration is not a proof of the field. -/
def Required (ch : NMX_R4_Authentication.Choices) : Prop :=
 ∀ (R0 : Bytes → Bytes → Prop) (w : Bytes → Bytes → Bytes → Spec (Except V0.VErr Unit)),
 TAS.Refines064 V0 AspisR1.NNH_064Install.f064 R0 w →
 TX2_242.RowSpec_242 L D (NMX_R6_Validation.validate ch) →
 RowSpec_241 L D (TAS.lib V0 R0 w) (NMX_R9_StageTwo.stage2 ch)

/-- Exact definitional field-type check; deliberately does not construct r241. -/
theorem exact_type {VL : VLib} (I0 : TAS.Impl L V0 VL) (ch : NMX_R4_Authentication.Choices) :
 Required ch =
 (∀ (R0 : Bytes → Bytes → Prop) (w : Bytes → Bytes → Bytes → Spec (Except V0.VErr Unit)),
 TAS.Refines064 V0 (install I0 ch).f064 R0 w →
 TX2_242.RowSpec_242 L D (install I0 ch).f242 →
 RowSpec_241 L D (TAS.lib V0 R0 w) (install I0 ch).f241) := rfl

/-- The TAS projection has exactly that type at the literal installation. -/
example {VL : VLib} (I0 : TAS.Impl L V0 VL) (ch : NMX_R4_Authentication.Choices)
 (roots : TAS.NMS_Roots L D V0 VL (install I0 ch)) : Required ch := roots.r241

#print axioms exact_type
end NNS_Field
