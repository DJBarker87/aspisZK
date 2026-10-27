import R1Z.PDict_Static222_03
set_option autoImplicit false
noncomputable section
namespace R1Z.PDict_Static222
open Aeneas Aeneas.Std ProverRwFull PDict_FormatterTypeMaps PDict_FormatterDictionaryMap
/-- Carrier transport candidate for `zeroize.Zeroize.Blanket`. -/
theorem erase_64 (base : ExternalTypes) (F : Type) (ops : @ExternalFuns base) :
    @zeroize.Zeroize.Blanket (types base F) (selected base F ops) = @zeroize.Zeroize.Blanket base ops := by
  delta zeroize.Zeroize.Blanket
  all_goals rfl
#print axioms erase_64

/-- Carrier transport candidate for `aspis_prover.state_only_entropy.Profile21SourceExpander.new`. -/
theorem erase_65 (base : ExternalTypes) (F : Type) (ops : @ExternalFuns base) :
    @aspis_prover.state_only_entropy.Profile21SourceExpander.new (types base F) (selected base F ops) = @aspis_prover.state_only_entropy.Profile21SourceExpander.new base ops := by
  delta aspis_prover.state_only_entropy.Profile21SourceExpander.new
  first | rfl | (try simp only [erase_62 base F ops, erase_64 base F ops]; all_goals rfl)
#print axioms erase_65

/-- Carrier transport candidate for `aspis_core.state_only_hiding.StateOnlyHidingContext.Insts.CoreCmpPartialEqStateOnlyHidingContext`. -/
theorem erase_66 (base : ExternalTypes) (F : Type) (ops : @ExternalFuns base) :
    @aspis_core.state_only_hiding.StateOnlyHidingContext.Insts.CoreCmpPartialEqStateOnlyHidingContext (types base F) (selected base F ops) = @aspis_core.state_only_hiding.StateOnlyHidingContext.Insts.CoreCmpPartialEqStateOnlyHidingContext base ops := by
  delta aspis_core.state_only_hiding.StateOnlyHidingContext.Insts.CoreCmpPartialEqStateOnlyHidingContext
  all_goals rfl
#print axioms erase_66

/-- Carrier transport candidate for `aspis_prover.state_only_entropy.ReservedStateOnlyAttemptSecrets.validate_pool_v1_context`. -/
theorem erase_67 (base : ExternalTypes) (F : Type) (ops : @ExternalFuns base) :
    @aspis_prover.state_only_entropy.ReservedStateOnlyAttemptSecrets.validate_pool_v1_context (types base F) (selected base F ops) = @aspis_prover.state_only_entropy.ReservedStateOnlyAttemptSecrets.validate_pool_v1_context base ops := by
  delta aspis_prover.state_only_entropy.ReservedStateOnlyAttemptSecrets.validate_pool_v1_context
  first | rfl | (try simp only [erase_66 base F ops]; all_goals rfl)
#print axioms erase_67

/-- Carrier transport candidate for `aspis_prover.state_only_entropy.source_inactive_step`. -/
theorem erase_68 (base : ExternalTypes) (F : Type) (ops : @ExternalFuns base) :
    @aspis_prover.state_only_entropy.source_inactive_step (types base F) (selected base F ops) = @aspis_prover.state_only_entropy.source_inactive_step base ops := by
  delta aspis_prover.state_only_entropy.source_inactive_step
  all_goals rfl
#print axioms erase_68

/-- Carrier transport candidate for `aspis_prover.state_only_entropy.source_inactive_sum_loop.body`. -/
theorem erase_69 (base : ExternalTypes) (F : Type) (ops : @ExternalFuns base) :
    @aspis_prover.state_only_entropy.source_inactive_sum_loop.body (types base F) (selected base F ops) = @aspis_prover.state_only_entropy.source_inactive_sum_loop.body base ops := by
  delta aspis_prover.state_only_entropy.source_inactive_sum_loop.body
  first | rfl | (try simp only [erase_68 base F ops]; all_goals rfl)
#print axioms erase_69

/-- Carrier transport candidate for `aspis_prover.state_only_entropy.source_inactive_sum_loop`. -/
theorem erase_70 (base : ExternalTypes) (F : Type) (ops : @ExternalFuns base) :
    @aspis_prover.state_only_entropy.source_inactive_sum_loop (types base F) (selected base F ops) = @aspis_prover.state_only_entropy.source_inactive_sum_loop base ops := by
  delta aspis_prover.state_only_entropy.source_inactive_sum_loop
  first | rfl | (try simp only [erase_69 base F ops]; all_goals rfl)
#print axioms erase_70

/-- Carrier transport candidate for `aspis_prover.state_only_entropy.source_inactive_sum`. -/
theorem erase_71 (base : ExternalTypes) (F : Type) (ops : @ExternalFuns base) :
    @aspis_prover.state_only_entropy.source_inactive_sum (types base F) (selected base F ops) = @aspis_prover.state_only_entropy.source_inactive_sum base ops := by
  delta aspis_prover.state_only_entropy.source_inactive_sum
  first | rfl | (try simp only [erase_70 base F ops]; all_goals rfl)
#print axioms erase_71

/-- Carrier transport candidate for `aspis_prover.state_only_entropy.balance_source_d`. -/
theorem erase_72 (base : ExternalTypes) (F : Type) (ops : @ExternalFuns base) :
    @aspis_prover.state_only_entropy.balance_source_d (types base F) (selected base F ops) = @aspis_prover.state_only_entropy.balance_source_d base ops := by
  delta aspis_prover.state_only_entropy.balance_source_d
  first | rfl | (try simp only [erase_71 base F ops]; all_goals rfl)
#print axioms erase_72

/-- Carrier transport candidate for `aspis_prover.state_only_entropy.pool_v1_private_attempt_binding`. -/
theorem erase_73 (base : ExternalTypes) (F : Type) (ops : @ExternalFuns base) :
    @aspis_prover.state_only_entropy.pool_v1_private_attempt_binding (types base F) (selected base F ops) = @aspis_prover.state_only_entropy.pool_v1_private_attempt_binding base ops := by
  delta aspis_prover.state_only_entropy.pool_v1_private_attempt_binding
  all_goals rfl
#print axioms erase_73

/-- Carrier transport candidate for `aspis_prover.state_only_entropy.Profile21SourceExpander.next_word`. -/
theorem erase_74 (base : ExternalTypes) (F : Type) (ops : @ExternalFuns base) :
    @aspis_prover.state_only_entropy.Profile21SourceExpander.next_word (types base F) (selected base F ops) = @aspis_prover.state_only_entropy.Profile21SourceExpander.next_word base ops := by
  delta aspis_prover.state_only_entropy.Profile21SourceExpander.next_word
  first | rfl | (try simp only [erase_62 base F ops, erase_64 base F ops]; all_goals rfl)
#print axioms erase_74

/-- Carrier transport candidate for `aspis_prover.state_only_entropy.Profile21SourceExpander.m31_loop.body`. -/
theorem erase_75 (base : ExternalTypes) (F : Type) (ops : @ExternalFuns base) :
    @aspis_prover.state_only_entropy.Profile21SourceExpander.m31_loop.body (types base F) (selected base F ops) = @aspis_prover.state_only_entropy.Profile21SourceExpander.m31_loop.body base ops := by
  delta aspis_prover.state_only_entropy.Profile21SourceExpander.m31_loop.body
  first | rfl | (try simp only [erase_74 base F ops]; all_goals rfl)
#print axioms erase_75

/-- Carrier transport candidate for `aspis_prover.state_only_entropy.Profile21SourceExpander.m31_loop`. -/
theorem erase_76 (base : ExternalTypes) (F : Type) (ops : @ExternalFuns base) :
    @aspis_prover.state_only_entropy.Profile21SourceExpander.m31_loop (types base F) (selected base F ops) = @aspis_prover.state_only_entropy.Profile21SourceExpander.m31_loop base ops := by
  delta aspis_prover.state_only_entropy.Profile21SourceExpander.m31_loop
  first | rfl | (try simp only [erase_75 base F ops]; all_goals rfl)
#print axioms erase_76

/-- Carrier transport candidate for `aspis_prover.state_only_entropy.Profile21SourceExpander.m31`. -/
theorem erase_77 (base : ExternalTypes) (F : Type) (ops : @ExternalFuns base) :
    @aspis_prover.state_only_entropy.Profile21SourceExpander.m31 (types base F) (selected base F ops) = @aspis_prover.state_only_entropy.Profile21SourceExpander.m31 base ops := by
  delta aspis_prover.state_only_entropy.Profile21SourceExpander.m31
  first | rfl | (try simp only [erase_76 base F ops]; all_goals rfl)
#print axioms erase_77

/-- Carrier transport candidate for `aspis_prover.state_only_entropy.Profile21SourceExpander.qm31`. -/
theorem erase_78 (base : ExternalTypes) (F : Type) (ops : @ExternalFuns base) :
    @aspis_prover.state_only_entropy.Profile21SourceExpander.qm31 (types base F) (selected base F ops) = @aspis_prover.state_only_entropy.Profile21SourceExpander.qm31 base ops := by
  delta aspis_prover.state_only_entropy.Profile21SourceExpander.qm31
  first | rfl | (try simp only [erase_77 base F ops]; all_goals rfl)
#print axioms erase_78

/-- Carrier transport candidate for `aspis_prover.state_only_entropy.sample_source_d_loop.body`. -/
theorem erase_79 (base : ExternalTypes) (F : Type) (ops : @ExternalFuns base) :
    @aspis_prover.state_only_entropy.sample_source_d_loop.body (types base F) (selected base F ops) = @aspis_prover.state_only_entropy.sample_source_d_loop.body base ops := by
  delta aspis_prover.state_only_entropy.sample_source_d_loop.body
  first | rfl | (try simp only [erase_78 base F ops]; all_goals rfl)
#print axioms erase_79
end R1Z.PDict_Static222
