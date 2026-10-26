import PoolS2_PolicyFacts
set_option autoImplicit false
noncomputable section
namespace AspisR1.PoolS2_PolicyExact
open Aeneas Aeneas.Std Result PoolS2_PolicySource PoolS2_PolicyFacts

theorem ready (p : Policy) (h : Valid p) :
    pool_v1.format.validate_verifier_policy_v1 p = ok (.Ok ()) := by
  classical
  rcases h with ⟨flags,registry,binding,coupled,authority⟩
  by_cases hi : immutable p = true <;> by_cases hd : deployment p = true
  all_goals simp_all [pool_v1.format.validate_verifier_policy_v1, Hist_Authority.keyEq,
    immutable, deployment, zero, lift]

  all_goals try split
  all_goals try split
  all_goals try simp_all
  all_goals scalar_tac

theorem accepted_iff (p : Policy) :
    pool_v1.format.validate_verifier_policy_v1 p = ok (.Ok ()) ↔ Valid p :=
  ⟨PoolS2_PolicyFacts.accepted p,ready p⟩

#print axioms ready
#print axioms accepted_iff
end AspisR1.PoolS2_PolicyExact
end
