import NNG_ReturnedPath137
import NNG_FinishReturn137
import NNG_Reached137
import NNG_VerifiedRoundtrip136
set_option autoImplicit false
noncomputable section
namespace AspisR1.NNG_Ready137
open Aeneas Aeneas.Std Result NMP_prepare NMP_Transport

theorem returned (a : NNG_Data137.Args) (obs : RSL.Observer) (env : RSL.Env)
 (domain : RSL.TX1_137.Domain NNG_Data137.VL a) (out : r1_semantic.Verified Unit)
 (native : NNG_Context137.emitted (NNG_Context137.calls env) (NNG_Context137.input a obs env)=.ok (.Ok out)) :
 NNG_VerifiedDomain136.Canonical (NNG_Output137.verified out) ∧
 LIBC_PreparedDomain.Semantic (toT11 out) := by
 obtain ⟨rawp,t,ch,after,parsed,publicCall,begun,finish⟩:=
  NNG_ReturnedPath137.returned env (NNG_Context137.input a obs env) out native
 obtain ⟨p,parseEval,same⟩:=NNG_Reached137.parse_eval a domain rawp parsed
 subst rawp
 let canonicalCh:=NNG_ChallengeProjection137.project NNG_ProjectionFallback137.zero (toT3 ch)
 have challenges : LIB_VCarriers.challengesRaw canonicalCh=toT3 ch :=
  NNG_Reached137.begin_raw NNG_ProjectionFallback137.zero env p t ch after begun
 have raw:=NNG_FinishReturn137.returned env (NNG_PublicSource137.digest env)
  (fromT9 a.public_) (fromT13 (LIB_VCarriers.prefixRaw p)) after ch (NNG_Context137.observer obs) out finish
 let input:=NNG_FinishAdapter137.childInput (NNG_PublicSource137.digest env)
  (toT9 (fromT9 a.public_)) (toT13 (fromT13 (LIB_VCarriers.prefixRaw p))) (toT10 after) (toT3 ch)
  (NNG_Context137.observer obs)
 have prefixEq : input.prefixValue=NNG_LIBData.lowerPrefix p := by
  simp only [input,NNG_FinishAdapter137.childInput,fromT13_inverse,NNG_LIBData.lowerPrefix]
 have chEq : input.challenges=NNG_LIBArrays.lowerChallenges canonicalCh := by
  change NNG_Transport.fromT3 (toT3 ch)=_
  rw [←challenges,←NNG_LIBTerminal.lower_challenges,NNG_Transport.toT3_inverse]
 have digestEq : input.digest=NNG_LIBDigest.digest env := rfl
 have ready:=NNG_FinishReady136.returned env input p prefixEq canonicalCh chEq digestEq
  (NNG_Output137.verified out) raw
 refine ⟨ready.1,?_⟩
 simpa only [NNG_Output137.verified,NNG_Transport.fromT11_inverse] using ready.2.2
#print axioms returned
end AspisR1.NNG_Ready137
