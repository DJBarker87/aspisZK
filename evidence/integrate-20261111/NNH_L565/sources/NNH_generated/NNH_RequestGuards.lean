import NNH_RequestOk
import NND_Constants
set_option autoImplicit false
noncomputable section
namespace NNH_RequestGuards
open Aeneas Aeneas.Std AdapterRw NND_Carrier NNH_Libraries
attribute [local instance] Classical.propDecidable

theorem value (q : LIBB_PoolCarriers.Request)
 (guards : (decide (L.reqProfile q ≠ RSL.PROFILE_BINDING) || decide (L.reqRelease q ≠ RSL.RELEASE_BINDING) || decide (L.reqPoolProgram q ≠ D.pool))=false) :
 q.verifier_profile=r1_pool_adapter.PROFILE_BINDING ∧ q.verifier_release=r1_pool_adapter.RELEASE_BINDING ∧ q.pool_program=unkey D.pool := by
 simp only [Bool.or_eq_false_iff,decide_eq_false_iff_not,not_not] at guards
 refine ⟨(key_eq_iff _ _).mp ?_,(key_eq_iff _ _).mp ?_,(key_eq_iff _ _).mp ?_⟩
 · exact guards.1.1.trans NND_Constants.profile.symm
 · exact guards.1.2.trans NND_Constants.release.symm
 · exact guards.2.trans (key_forth D.pool).symm
#print axioms value
end NNH_RequestGuards
