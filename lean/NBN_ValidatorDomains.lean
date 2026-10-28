import NBH_Audit
set_option autoImplicit false
set_option linter.unusedSimpArgs false
noncomputable section
namespace NBN_ValidatorDomains
open Aeneas Aeneas.Std Result
open NBD_DigestInduction NBH_Frontier

theorem afterstate (a : NBH_Validators.Afterstate)
    (valid : NBH_Validators.afterResult a = .Ok ()) :
    0 < a.next_pair_index.val ∧ a.next_pair_index.val ≤ 1048576 ∧
    Canonical a.next_root ∧ CanonicalFrom a.next_frontier 0 := by
  unfold NBH_Validators.afterResult at valid
  split at valid
  · cases valid
  · rename_i index
    split at valid
    · rename_i digest
      exact ⟨by omega,by omega,digest⟩
    · cases valid

theorem live (s : NBH_LiveValidator.Snapshot)
    (valid : NBH_LiveValidator.result s = .Ok ()) :
    s.pool ≠ Array.repeat 32#usize 0#u8 ∧
    s.deployment_domain ≠ Array.repeat 32#usize 0#u8 ∧
    s.sequence = s.next_pair_index ∧ s.next_pair_index.val < 1048576 ∧
    Canonical s.current_root ∧ CanonicalFrom s.frontier 0 := by
  unfold NBH_LiveValidator.result at valid
  split at valid
  · cases valid
  · rename_i bindings
    split at valid
    · cases valid
    · rename_i sequence
      split at valid
      · cases valid
      · rename_i capacity
        split at valid
        · rename_i digests
          exact ⟨fun h => bindings (Or.inl h),fun h => bindings (Or.inr h),
            not_not.mp sequence,by omega,digests⟩
        · cases valid

theorem after_row (a : NBH_Validators.Afterstate)
    (valid : NBH_Validators.afterResult a = .Ok ()) (j : Fin 20) :
    Canonical (a.next_frontier.val[j.val]'(by have := a.next_frontier.property; scalar_tac)) :=
  (afterstate a valid).2.2.2 j (by omega)

theorem live_row (s : NBH_LiveValidator.Snapshot)
    (valid : NBH_LiveValidator.result s = .Ok ()) (j : Fin 20) :
    Canonical (s.frontier.val[j.val]'(by have := s.frontier.property; scalar_tac)) :=
  (live s valid).2.2.2.2.2 j (by omega)

#print axioms afterstate
#print axioms live
#print axioms after_row
#print axioms live_row
end NBN_ValidatorDomains
