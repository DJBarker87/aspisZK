import NNG_DomExtra136
set_option autoImplicit false
noncomputable section
namespace AspisR1.NNG_DomRecord25_136
open Aeneas Aeneas.Std Result NNG_verify_finish NNG_Emitted NMT_CallTree NNG_Transport
open NNG_TraceAll136 NNG_TypedDomains136 NNG_LIBScalar NNG_LIBArrayDomain

theorem record25 {W : Type} (fallback : Value) (c : Calls) (env : RSL.Env) (source : NNG_SourceCalls136.Sources c env)
    (s : Parent Unit W) (p : LIB_VCarriers.Prefix) (prefixEq : s.prefixValue=NNG_LIBData.lowerPrefix p)
    (running terminal mask : Q) (alpha : Alpha) (claims : Claims) (t1 : r1_wire.SemanticTranscript Unit)
    (etaDom : Domain s.challenges.eta) (terminalDom : Domain terminal) (maskDom : Domain mask) :
    All Checked (NNG_TreeSuffixes.f_r4 c s running terminal mask alpha t1 claims) := by
  obtain ⟨rec,field,domain⟩ := LIB_VRecordDomains.extra p
  have native := NNG_GetterReturn136.returned p 25#u8 rec field
  have frame := NNG_LIBRecordFrame.circle_domain p ⟨25,by decide⟩ (fromT14 rec) native
  have decode : LIB_VDecode.Domain (toT14 (fromT14 rec)) 87 := by
    rw [fromT14_inverse]
    exact domain
  unfold NNG_TreeSuffixes.f_r4
  dsimp only
  rw [source.record,prefixEq,native]
  refine NNG_AllInvokeOk136.invoke_ok Checked "record25" _
    (core.result.Result.Ok (fromT14 rec) : core.result.Result r1_wire.ValidatedRecord r1_wire.Error) _ (NNG_CheckedCalls136.record25 _ _) ?_
  change All Checked (NNG_TreeSuffixes.f_r5 c s running terminal mask alpha t1 claims (fromT14 rec) (.Ok (fromT14 rec)))
  exact NNG_DomExtra136.extra fallback c env source s p prefixEq running terminal mask alpha claims t1
    (fromT14 rec) frame decode etaDom terminalDom maskDom
#print axioms record25
end AspisR1.NNG_DomRecord25_136
