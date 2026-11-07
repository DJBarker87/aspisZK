import NND_MissingPartial
import NMN_064
set_option autoImplicit false
noncomputable section
namespace NND_064ParseTransport
open Aeneas Aeneas.Std Result AspisR1 VTop_Stages
/-- Both parser adapters map the SAME complete frozen parser Result. -/
theorem shape_parse (proof : Slice U8) : Tx2I_Install.shape proof = NLE_ParseInstall.parse proof := by
 unfold Tx2I_Install.shape NLE_ParseInstall.parse
 cases h : Op3I_Source.verifier.candidate.parse_shape Op3I_Std.ops proof with
 | fail e => rfl
 | div => rfl
 | ok r => cases r <;> rfl

theorem sdk_op11 {F C X : Type} (c : DrvC_Installation.Configuration F C)
 (D : AdapterRw.aspis_core.digest.Digest32 X) (p q r : Slice U8) (x : X)
 (obs : Option (AdapterRw.aspis_r1_cost_probe.verifier.Phase → Result Unit)) :
 (DrvC_Installation.sdk c).op11 D p q r x obs =
 verifier.candidate.tx2_authenticated (DrvC_Installation.stage c) D p q r x obs := rfl

theorem stage_parse {F C : Type} (c : DrvC_Installation.Configuration F C)
 (proof : Slice U8) : (DrvC_Installation.stage c).op3 proof = NLE_ParseInstall.parse proof :=
 shape_parse proof

#print axioms shape_parse
#print axioms sdk_op11
#print axioms stage_parse
end NND_064ParseTransport
