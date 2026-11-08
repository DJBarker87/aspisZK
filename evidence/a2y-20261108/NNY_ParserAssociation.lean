import NNY_NNUParent
set_option autoImplicit false
noncomputable section
namespace AspisR1.NNY_ParserAssociation
open Aeneas Aeneas.Std Result VTop_Stages
/-- The actual installed parser and the adopted source share the same raw
parser call; only their finite enum maps differ syntactically. -/
theorem source (m : IDa_Deployed.Uninstalled NFN_NEW_GeometryDictionary.CE)
 (env : RSL.Env) (err : NFN_NEW_GeometryDictionary.CE) (r : NP6_StdModel.Reservation)
 (proof : Slice U8) :
 (NNH_Tx2SlotTransport.stage m env err r).op3 proof=NLE_ParseInstall.parse proof := by
 change Tx2I_Install.shape proof=NLE_ParseInstall.parse proof
 unfold Tx2I_Install.shape NLE_ParseInstall.parse
 cases raw : Op3I_Source.verifier.candidate.parse_shape Op3I_Std.ops proof with
 | fail e => simp only [raw,bind_tc_fail]
 | div => simp only [raw,bind_tc_div]
 | ok reply =>
  simp only [raw,bind_tc_ok]
  cases reply with
  | Err e => cases e <;> rfl
  | Ok v => cases v <;> rfl
#print axioms source
end AspisR1.NNY_ParserAssociation
end
