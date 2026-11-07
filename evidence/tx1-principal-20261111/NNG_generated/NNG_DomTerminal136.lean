import NNG_DomPublicMap136
import NNG_TerminalReturned136
set_option autoImplicit false
noncomputable section
namespace AspisR1.NNG_DomTerminal136
open Aeneas Aeneas.Std Result NNG_verify_finish NNG_Emitted NMT_CallTree NNG_Transport
open NNG_TraceAll136 NNG_TypedDomains136 NNG_LIBScalar NNG_LIBArrays NNG_LIBArrayDomain NNG_LIBClaimsDomain

theorem terminal {W : Type} (fallback : Value) (c : Calls) (env : RSL.Env) (source : NNG_SourceCalls136.Sources c env)
    (s : Parent Unit W) (p : LIB_VCarriers.Prefix) (prefixEq : s.prefixValue=NNG_LIBData.lowerPrefix p)
    (pub : LIB_VCarriers.Public) (publicEq : s.publicValue=fromT9 pub)
    (orig : LIB_VCarriers.OrigChallenges) (origEq : s.challenges=lowerChallenges orig)
    (publicDom : LIB_VPublicDomain.publicDom pub)
    (running : Q) (alpha : Alpha) (claims : Claims) (t1 : r1_wire.SemanticTranscript Unit)
    (alphaDom : DomainArray alpha) (claimsDom : DomainClaims claims) :
    All Checked (NNG_TreeSuffixes.f_r2 c s running alpha t1 claims) := by
  have etaDom : Domain s.challenges.eta := by
    rw [origEq]
    exact lower_domain orig.eta
  unfold NNG_TreeSuffixes.f_r2
  refine NNG_TraceAll136.bind Checked
    (NMT_CallTree.invoke "terminal" (s.publicValue,claims,alpha,s.challenges) (c.c7 s.publicValue claims alpha s.challenges)) _ ?_ ?_
  · exact NNG_TraceAll136.invoke Checked _ _ _ (NNG_CheckedCalls136.terminal _ _ ⟨claimsDom,alphaDom⟩)
  · intro reply returned
    rw [NMT_CallTree.run_result,NMT_CallTree.erase_invoke] at returned
    rw [source.terminal,publicEq,origEq] at returned
    cases reply with
    | Ok q =>
      have qDom := NNG_TerminalReturned136.canonical fallback pub claims alpha orig q claimsDom alphaDom publicDom returned
      exact NNG_DomPublicMap136.ok fallback c env source s p prefixEq running q alpha claims t1 etaDom qDom alphaDom claimsDom
    | Err e => exact NNG_DomPublicMap136.error c env source s running alpha claims t1 e
#print axioms terminal
end AspisR1.NNG_DomTerminal136
