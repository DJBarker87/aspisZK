import PCB_RegistryRef.Funs
import NGK_NFV_RequestGuards
set_option autoImplicit false
open Aeneas Aeneas.Std Result
namespace PCB_RegistryLaws
open PCB_RegistryRef

theorem matches (s : AuthenticatedVerifierSelectionV1)
    (p v q r : Array U8 32#usize) (version : U8) :
    matches_ref s p v q r version = ok (decide
      (s.pool.val = p.val ∧ s.verifier_program.val = v.val ∧
       s.profile_binding.val = q.val ∧ s.release_binding.val = r.val ∧
       s.statement_version = version)) := by
  by_cases h0 : s.pool.val = p.val <;>
    by_cases h1 : s.verifier_program.val = v.val <;>
    by_cases h2 : s.profile_binding.val = q.val <;>
    by_cases h3 : s.release_binding.val = r.val <;>
    simp [matches_ref, NGK_NFV_RequestGuards.array, h0,h1,h2,h3]

theorem owner (s : AuthenticatedVerifierSelectionV1) (p : Pubkey) :
    owner_ref s p = ok (match s.expected_verifier_loader with
      | none => true
      | some expected => decide (p.val = expected.val)) := by
  cases h : s.expected_verifier_loader <;>
    simp [owner_ref,h,Pubkey.to_bytes,NGK_NFV_RequestGuards.array]

#print axioms matches
#print axioms owner
end PCB_RegistryLaws
