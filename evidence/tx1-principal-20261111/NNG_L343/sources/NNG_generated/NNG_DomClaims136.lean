import NNG_DomTerminal136
set_option autoImplicit false
noncomputable section
namespace AspisR1.NNG_DomClaims136
open Aeneas Aeneas.Std Result NNG_verify_finish NNG_Emitted NMT_CallTree NNG_Transport
open NNG_TraceAll136 NNG_TypedDomains136 NNG_LIBScalar NNG_LIBArrays NNG_LIBArrayDomain NNG_LIBClaimsDomain

theorem claims {W : Type} (fallback : Value) (c : Calls) (env : RSL.Env) (source : NNG_SourceCalls136.Sources c env)
    (s : Parent Unit W) (p : LIB_VCarriers.Prefix) (prefixEq : s.prefixValue=NNG_LIBData.lowerPrefix p)
    (pub : LIB_VCarriers.Public) (publicEq : s.publicValue=fromT9 pub)
    (orig : LIB_VCarriers.OrigChallenges) (origEq : s.challenges=lowerChallenges orig)
    (publicDom : LIB_VPublicDomain.publicDom pub)
    (running : Q) (alpha : Alpha) (t1 : r1_wire.SemanticTranscript Unit) (alphaDom : DomainArray alpha) :
    All Checked (NNG_TreeSuffixes.f_r1 c s running alpha t1) := by
  unfold NNG_TreeSuffixes.f_r1
  refine NNG_TraceAll136.bind Checked (NMT_CallTree.invoke "claims" s.prefixValue (c.c8 s.prefixValue)) _ ?_ ?_
  · exact NNG_TraceAll136.invoke Checked _ _ _ (NNG_CheckedCalls136.claims _ _)
  · intro reply returned
    rw [NMT_CallTree.run_result,NMT_CallTree.erase_invoke] at returned
    rw [source.claims,prefixEq] at returned
    cases reply with
    | Ok claims =>
      have claimsDom := NNG_LIBClaimsDomain.returned env p claims returned
      change All Checked (NNG_TreeSuffixes.f_r2 c s running alpha t1 claims)
      exact NNG_DomTerminal136.terminal fallback c env source s p prefixEq pub publicEq orig origEq publicDom
        running alpha claims t1 alphaDom claimsDom
    | Err e => intro event member;cases member
#print axioms claims

theorem mark2 {W : Type} (fallback : Value) (c : Calls) (env : RSL.Env) (source : NNG_SourceCalls136.Sources c env)
    (s : Parent Unit W) (p : LIB_VCarriers.Prefix) (prefixEq : s.prefixValue=NNG_LIBData.lowerPrefix p)
    (pub : LIB_VCarriers.Public) (publicEq : s.publicValue=fromT9 pub)
    (orig : LIB_VCarriers.OrigChallenges) (origEq : s.challenges=lowerChallenges orig)
    (publicDom : LIB_VPublicDomain.publicDom pub)
    (running : Q) (alpha : Alpha) (t1 : r1_wire.SemanticTranscript Unit) (alphaDom : DomainArray alpha) :
    All Checked (NNG_TreeSuffixes.f_mark2 c s running alpha t1) := by
  unfold NNG_TreeSuffixes.f_mark2
  refine NNG_TraceAll136.bind Checked (NMT_CallTree.invoke "mark2" (s.observer,2#u8) (c.c9 s.observer 2#u8)) _ ?_ ?_
  · exact NNG_TraceAll136.invoke Checked _ _ _ (NNG_CheckedCalls136.mark2 _ _)
  · intro u returned
    cases u
    exact claims fallback c env source s p prefixEq pub publicEq orig origEq publicDom running alpha t1 alphaDom
#print axioms mark2
end AspisR1.NNG_DomClaims136
