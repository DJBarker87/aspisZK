import NNG_DomArrays136
import NNG_DPublicMap136
set_option autoImplicit false
noncomputable section
namespace AspisR1.NNG_DomPublicMap136
open Aeneas Aeneas.Std Result NNG_verify_finish NNG_Emitted NMT_CallTree NNG_Transport
open NNG_TraceAll136 NNG_TypedDomains136 NNG_LIBScalar NNG_LIBArrayDomain NNG_LIBClaimsDomain

theorem ok {W : Type} (fallback : Value) (c : Calls) (env : RSL.Env) (source : NNG_SourceCalls136.Sources c env)
    (s : Parent Unit W) (p : LIB_VCarriers.Prefix) (prefixEq : s.prefixValue=NNG_LIBData.lowerPrefix p)
    (running terminal : Q) (alpha : Alpha) (claims : Claims) (t1 : r1_wire.SemanticTranscript Unit)
    (etaDom : Domain s.challenges.eta) (terminalDom : Domain terminal) (alphaDom : DomainArray alpha) (claimsDom : DomainClaims claims) :
    All Checked (NNG_TreeSuffixes.f_r3 c s running alpha t1 claims (.Ok terminal)) := by
  unfold NNG_TreeSuffixes.f_r3
  dsimp only
  rw [source.mapErr,NNG_DPublicMap136.source]
  change All Checked (NNG_TreeSuffixes.f_mark3 c s running terminal alpha t1 claims)
  exact NNG_DomArrays136.mark3 fallback c env source s p prefixEq running terminal alpha claims t1 etaDom terminalDom alphaDom claimsDom
#print axioms ok

theorem error {W : Type} (c : Calls) (env : RSL.Env) (source : NNG_SourceCalls136.Sources c env)
    (s : Parent Unit W) (running : Q) (alpha : Alpha) (claims : Claims) (t1 : r1_wire.SemanticTranscript Unit)
    (e : aspis_core.state_only_prefix.r0.Error) :
    All Checked (NNG_TreeSuffixes.f_r3 c s running alpha t1 claims (.Err e)) := by
  unfold NNG_TreeSuffixes.f_r3
  dsimp only
  rw [source.mapErr,NNG_DPublicMap136.source]
  intro event member
  cases member
#print axioms error
end AspisR1.NNG_DomPublicMap136
