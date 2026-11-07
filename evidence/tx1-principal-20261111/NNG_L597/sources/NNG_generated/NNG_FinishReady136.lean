import NNG_LegacyReturnMaps136
import NNG_LegacyDigest136
import NNG_VerifiedDomain136
import LIBC_PreparedDomain
set_option autoImplicit false
noncomputable section
namespace AspisR1.NNG_FinishReady136
open Aeneas Aeneas.Std Result NNG_verify_finish NNG_Emitted NNG_Transport
open NMT_Transport (arr)

theorem returned {W : Type} (env : RSL.Env) (s : Parent Unit W)
 (p : LIB_VCarriers.Prefix) (prefixEq : s.prefixValue=NNG_LIBData.lowerPrefix p)
 (c : LIB_VCarriers.Challenges) (challengeEq : s.challenges=NNG_LIBArrays.lowerChallenges c)
 (digestEq : s.digest=NNG_LIBDigest.digest env) (out : r1_semantic.Verified Unit)
 (native : NNG_Emitted.emitted (NNG_ConcreteCalls136.calls env) s=.ok (.Ok out)) :
 NNG_VerifiedDomain136.Canonical out ∧ env.reservation=true ∧
 LIBC_PreparedDomain.Semantic (toT11 out) := by
 have finish := NNG_ModelSuccess136.finish env s out native
 obtain ⟨running,t25,record25,record26,z0,t26,z1,t27,rounds,challenges,state,transcript,
   claimCall,read25,extra,circle0,read26,before,circle1,z⟩ :=
   AspisR1PublicPreparation.S1SemanticFinishBounds.finish_success AspisS1ExtractedRoundChildren.children
     (NNG_LegacyConfig136.boundaries env) (NNG_Install.digest s.digest) (toT9 s.publicValue)
     (toT12 s.prefixValue) (toT10 s.transcript) (toT3 s.challenges) none (toT11 out) finish
 change toT3 out.challenges=toT3 s.challenges at challenges
 have sameChallenges : out.challenges=s.challenges := by
   have same := congrArg fromT3 challenges
   simpa only [toT3_inverse] using same
 change AspisR1PublicPreparation.RoundModel.rounds AspisS1ExtractedRoundChildren.children
   (NNG_Install.digest s.digest) (toT12 s.prefixValue) (toT10 s.transcript)=
   .ok (.Ok (running,arr toT1 out.alpha,t25)) at rounds
 have rawRounds := NNG_LegacyReturnMaps136.rounds s.digest s.prefixValue s.transcript running out.alpha t25 rounds
 rw [prefixEq] at rawRounds
 have alphaDom := (NNG_LIBRoundsCanonical.returned p s.digest s.transcript (fromT1 running) out.alpha (fromT10 t25) rawRounds).2
 change (NNG_LegacyConfig136.boundaries env).claims (toT12 s.prefixValue)=
   .ok (.Ok (NNG_InstallClaims.lowerClaims out.claims)) at claimCall
 have rawClaims := NNG_LegacyReturnMaps136.claims env s.prefixValue out.claims claimCall
 rw [prefixEq] at rawClaims
 have claimsDom := NNG_LIBClaimsDomain.returned env p out.claims rawClaims
 change AspisS1ExtractedRoundChildren.children.decode 29#usize record25 87#usize=.ok (.Ok (arr toT1 out.extra)) at extra
 change AspisS1ExtractedRoundChildren.children.decode 29#usize record26 0#usize=.ok (.Ok (arr toT1 out.before_z1)) at before
 have extraDom := NNG_DecodeReturned136.canonical 29#usize (fromT14 record25) 87#usize out.extra
   (NNG_LegacyReturnMaps136.decode 29#usize record25 87#usize out.extra extra)
 have beforeDom := NNG_DecodeReturned136.canonical 29#usize (fromT14 record26) 0#usize out.before_z1
   (NNG_LegacyReturnMaps136.decode 29#usize record26 0#usize out.before_z1 before)
 have reservation : env.reservation=true := by
   have combined := rawClaims.symm.trans (NNG_LIBClaims.call_model env p)
   cases h : env.reservation with
   | false=>
     simp only [h,Bool.false_eq_true,if_false] at combined
     cases combined
   | true=>rfl
 refine ⟨⟨⟨c,sameChallenges.trans challengeEq⟩,alphaDom,claimsDom,extraDom,beforeDom⟩,reservation,?_⟩
 have configEq : {NNG_LegacyConfig136.boundaries env with
   claims:=AspisR1PublicPreparation.ClaimsUnrolledFinish.claims (NP6_StdModel.calls (.Ok ()))}=
   NNG_LegacyConfig136.boundaries env := by
   unfold NNG_LegacyConfig136.boundaries
   simp only [NNG_LIBClaims.reservation,reservation,if_true]
 have digest : NNG_Install.digest s.digest=NGQ_Effects.dictionary (LIB_Env.hashv env) :=
   (congrArg NNG_Install.digest digestEq).trans (NNG_LegacyDigest136.supplied env)
 refine ⟨NNG_LegacyConfig136.boundaries env,LIB_Env.hashv env,toT9 s.publicValue,toT12 s.prefixValue,
   toT10 s.transcript,toT3 s.challenges,none,?_⟩
 rw [configEq,←digest]
 exact finish
#print axioms returned
end AspisR1.NNG_FinishReady136
