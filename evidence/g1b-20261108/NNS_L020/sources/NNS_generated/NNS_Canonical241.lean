import NNS_Field
set_option autoImplicit false
namespace NNS_Canonical241
open RSL RSL.TX2_241 NNS_Fold241

/-- Reused credited canonical statement only. This is NOT a specialization of
the missing parametric root and earns no new row or G1b credit. -/
theorem reused (ch : NMX_R4_Authentication.Choices) :
 RowSpec_241 L D V0 (NMX_R9_StageTwo.stage2 ch) := NMX_R9_StageTwo.root ch

/-- Canonical library normalization preserves the exact credited root type. -/
theorem canonical_type (ch : NMX_R4_Authentication.Choices) :
 RowSpec_241 L D (TAS.lib V0 V0.Root0 V0.tx2auth) (NMX_R9_StageTwo.stage2 ch) =
 RowSpec_241 NMX_R9_StageTwo.L NMX_R9_StageTwo.D NMX_R9_StageTwo.V
  (NMX_R9_StageTwo.stage2 ch) := rfl

#print axioms reused
#print axioms canonical_type
end NNS_Canonical241
