import NNG_DomCircle1_136
import NNG_GetterReturn136
import NNG_AllInvokeOk136
import NNG_SourceCalls136
set_option autoImplicit false
noncomputable section
namespace AspisR1.NNG_DomRecord26_136
open Aeneas Aeneas.Std Result NNG_verify_finish NNG_Emitted NMT_CallTree NNG_Transport
open NNG_TraceAll136 NNG_TypedDomains136

theorem record26 {W : Type} (c : Calls) (env : RSL.Env) (source : NNG_SourceCalls136.Sources c env)
    (s : Parent Unit W) (p : LIB_VCarriers.Prefix) (prefixEq : s.prefixValue=NNG_LIBData.lowerPrefix p)
    (alpha : Alpha) (claims : Claims) (extra : K29) (state : Array U8 32#usize)
    (z0 : aspis_core.circle.SecureCirclePoint) (t2 : r1_wire.SemanticTranscript Unit) :
    All Checked (NNG_TreeSuffixes.f_r7 c s alpha claims extra state t2 z0) := by
  obtain ⟨rec,field,domain⟩ := LIB_VRecordDomains.beforeZ1 p
  have native := NNG_GetterReturn136.returned p 26#u8 rec field
  have frame := NNG_LIBRecordFrame.circle_domain p ⟨26,by decide⟩ (fromT14 rec) native
  have decode : LIB_VDecode.Domain (toT14 (fromT14 rec)) 0 := by
    rw [fromT14_inverse]
    exact domain
  unfold NNG_TreeSuffixes.f_r7
  dsimp only
  rw [source.record,prefixEq,native]
  refine NNG_AllInvokeOk136.invoke_ok Checked "record26" _ (core.result.Result.Ok (fromT14 rec) : core.result.Result r1_wire.ValidatedRecord r1_wire.Error) _ (NNG_CheckedCalls136.record26 _ _) ?_
  change All Checked (NNG_TreeSuffixes.f_r8 c s alpha claims extra state t2 z0 (fromT14 rec) (.Ok (fromT14 rec)))
  exact NNG_DomCircle1_136.beforeZ1 c s alpha claims extra state z0 t2 (fromT14 rec) frame decode
#print axioms record26
end AspisR1.NNG_DomRecord26_136
