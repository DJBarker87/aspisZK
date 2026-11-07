import NNG_DomClaims136
import NNG_LIBRoundsCanonical
set_option autoImplicit false
noncomputable section
namespace AspisR1.NNG_DomRounds136
open Aeneas Aeneas.Std Result NNG_verify_finish NNG_Emitted NMT_CallTree NNG_Transport
open NNG_TraceAll136 NNG_TypedDomains136 NNG_LIBScalar NNG_LIBArrays NNG_LIBArrayDomain

theorem rounds {W : Type} (fallback : Value) (c : Calls) (env : RSL.Env) (source : NNG_SourceCalls136.Sources c env)
    (s : Parent Unit W) (p : LIB_VCarriers.Prefix) (prefixEq : s.prefixValue=NNG_LIBData.lowerPrefix p)
    (pub : LIB_VCarriers.Public) (publicEq : s.publicValue=fromT9 pub)
    (orig : LIB_VCarriers.OrigChallenges) (origEq : s.challenges=lowerChallenges orig)
    (publicDom : LIB_VPublicDomain.publicDom pub) :
    All Checked (NNG_TreeSuffixes.f_r c s) := by
  unfold NNG_TreeSuffixes.f_r
  refine NNG_TraceAll136.bind Checked
    (NMT_CallTree.invoke "rounds" (s.prefixValue,s.transcript) (c.c10 s.digest s.prefixValue s.transcript)) _ ?_ ?_
  · exact NNG_TraceAll136.invoke Checked _ _ _ (NNG_CheckedCalls136.rounds _ _)
  · intro reply returned
    rw [NMT_CallTree.run_result,NMT_CallTree.erase_invoke] at returned
    rw [source.rounds,prefixEq] at returned
    cases reply with
    | Ok val =>
      rcases val with ⟨running,alpha,t1⟩
      have canonical := NNG_LIBRoundsCanonical.returned p s.digest s.transcript running alpha t1 returned
      change All Checked (NNG_TreeSuffixes.f_mark2 c s running alpha t1)
      exact NNG_DomClaims136.mark2 fallback c env source s p prefixEq pub publicEq orig origEq publicDom
        running alpha t1 canonical.2
    | Err e => intro event member;cases member
#print axioms rounds
end AspisR1.NNG_DomRounds136
