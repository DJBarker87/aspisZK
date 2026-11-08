import NNH_Run5bCurrentShape
import LIB_VParsePrefix
set_option autoImplicit false
noncomputable section
namespace AspisR1.NNV_SemanticParse
open Aeneas Aeneas.Std Result

theorem association (source : Slice U8) :
 AspisR1PublicPreparation.PrefixAdapter.parseAccepted source =
 NGX_PrefixCarrier.result (AspisR1PrefixAggregateParser.r1_wire.Prefix.parse source) := by
 unfold AspisR1PublicPreparation.PrefixAdapter.parseAccepted NGX_PrefixCarrier.result
 apply bind_congr
 intro reply
 cases reply with
 | Ok p => rfl
 | Err e => cases e <;> rfl

theorem returned (source : Slice U8) (p : LIB_VCarriers.Prefix) (env : RSL.Env)
 (called : LIB_VLib.parsePrefixValue (LIB_Carriers.bytes source) env = .ok p) :
 AspisR1PublicPreparation.PrefixAdapter.parseAccepted source = .ok (.Ok (LIB_VCarriers.prefixRaw p)) := by
 change LIB_VResult.value id (.error (.Length 0#u8))
  (LIB_VParsePrefix.model (LIB_Carriers.bytes source)) = .ok p at called
 rw [LIB_VParsePrefix.model_same] at called
 have raw := LIB_VParsePrefix.raw_exact source
 cases model : LIB_VParsePrefix.parseRaw source with
 | fail e => rw [model] at called; cases called
 | div => rw [model] at called; cases called
 | ok reply =>
  rw [model] at called
  change reply = .ok p at called
  subst reply
  rw [model,bind_tc_ok] at raw
  exact (association source).trans raw.symm
#print axioms association
#print axioms returned
end AspisR1.NNV_SemanticParse
end
