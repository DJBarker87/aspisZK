import LPb_CheckpointPrefixes
import LPb_ClaimFailure
set_option autoImplicit false
open Aeneas Aeneas.Std Result
namespace LPb_Nonvacuity
/-- Nonempty primitive-stage domains, not a joint actual-top execution. -/
theorem query_domain : ∃ q : LPb_Logged.Query, q = [] := ⟨[],rfl⟩
theorem scalar_index_domain : ∃ l : Nat, l < 29 := ⟨28,by omega⟩
theorem weight_index_domain : ∃ i : Nat, i < 64 := ⟨63,by omega⟩
theorem scalar_rejection_domain : ∃ x : Nat, 2147483647 ≤ x ∧ x ≤ 4294967295 :=
  ⟨4294967295,by omega,by omega⟩
theorem attempted_failure_witness :
    ∃ (tr : List LPb_Logged.Query) (r : Result Unit),
      LPb_Logged.bind (tr,r) (fun _ => LPb_Logged.lift (ok ())) = (tr,fail .panic) :=
  ⟨[[]],fail .panic,rfl⟩
#print axioms query_domain
#print axioms scalar_index_domain
#print axioms weight_index_domain
#print axioms scalar_rejection_domain
#print axioms attempted_failure_witness
end LPb_Nonvacuity
