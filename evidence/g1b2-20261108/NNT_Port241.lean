import NNT_Verify241
set_option autoImplicit false
noncomputable section
namespace NNT_Port241
open RSL RSL.TX2_241 RSL.NNT NNS_Fold241

theorem root (ch : NMX_R4_Authentication.Choices)
 (R0 : Bytes → Bytes → Prop) (w : Bytes → Bytes → Bytes → Spec (Except V0.VErr Unit))
 (h : LawRefines V0 R0 w)
 (h242 : TX2_242.RowSpec_242 L D (NMX_R6_Validation.validate ch)) :
 RowSpec_241 L D (TAS.lib V0 R0 w) (NMX_R7_Port241.stage2 ch) :=
 NNS_PortLaw241.root ch R0 w
  (fun x env d => h x env _ d (NNT_Verify241.verify_law x env)) h242
#print axioms root
end NNT_Port241
