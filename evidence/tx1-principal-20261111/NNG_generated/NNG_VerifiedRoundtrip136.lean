import NNG_RawProjection136
import NNG_LIBTerminal
import NNG_PublicSource137
set_option autoImplicit false
noncomputable section
namespace AspisR1.NNG_VerifiedRoundtrip136
open Aeneas Aeneas.Std NNG_verify_finish NNG_Emitted NNG_Transport
open NNG_LIBScalar NNG_LIBArrays
open NMT_Transport (arr)

theorem challenges (fallback : Value) (v : r1_semantic.Verified Unit) (domain : NNG_VerifiedDomain136.Canonical v) :
 LIB_VCarriers.challengesRaw (projectChallenges fallback v.challenges)=toT3 v.challenges := by
 obtain ⟨c,same⟩ := domain.challenges
 rw [same,project_lower_challenges,NNG_LIBTerminal.lower_challenges]

theorem pair_map {A B : Type} (f : A → B) (a : Array A 2#usize) :
 Array.make 2#usize [f (NNG_Array136.get a 0#usize (by decide)),f (NNG_Array136.get a 1#usize (by decide))]=arr f a := by
 rw [←NNG_ArrayTwo136.eta a]
 rfl

theorem verified (fallback : Value) (v : r1_semantic.Verified Unit) (domain : NNG_VerifiedDomain136.Canonical v) :
 LIBC_PreparedCarriers.verified LIB_Prepared.types
  (NNG_DProjection136.verified (NNG_ProjectionFallback137.representation fallback) v)=toT11 v := by
 have hc := challenges fallback v domain
 have ha := NNG_RawProjection136.array_raw fallback v.alpha domain.alpha
 have hcl := NNG_RawProjection136.claims_raw fallback v.claims domain.claims
 have he := NNG_RawProjection136.array_raw fallback v.extra domain.extra
 have hb := NNG_RawProjection136.array_raw fallback v.before_z1 domain.beforeZ1
 simp only [LIBC_PreparedCarriers.verified,LIB_Prepared.types,NNG_DProjection136.verified,
  NNG_ProjectionFallback137.representation,NNG_Transport.toT11,hc,ha,hcl,he,hb,
  NNG_PublicSource137.key_native]
 congr 1
 · exact NNG_ArrayTwo136.eta _
 · exact pair_map toT2 v.z
#print axioms challenges
#print axioms pair_map
#print axioms verified
end AspisR1.NNG_VerifiedRoundtrip136
