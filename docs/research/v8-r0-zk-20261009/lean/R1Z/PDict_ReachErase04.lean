import R1Z.PDict_ReachErase03
set_option autoImplicit false
noncomputable section
namespace R1Z.PDict_ReachErase
open Aeneas Aeneas.Std ProverRwFull
variable [ExternalTypes]

/-- Full symbolic source-function equality for `zeroize.Zeroize.Blanket`. -/
theorem erase_64 (ops other : ExternalFuns) :
    @zeroize.Zeroize.Blanket _ (replace ops other) = @zeroize.Zeroize.Blanket _ ops := by
  delta zeroize.Zeroize.Blanket
  all_goals rfl
#print axioms erase_64

/-- Full symbolic source-function equality for `aspis_prover.state_only_entropy.Profile21SourceExpander.new`. -/
theorem erase_65 (ops other : ExternalFuns) :
    @aspis_prover.state_only_entropy.Profile21SourceExpander.new _ (replace ops other) = @aspis_prover.state_only_entropy.Profile21SourceExpander.new _ ops := by
  delta aspis_prover.state_only_entropy.Profile21SourceExpander.new
  first | rfl | (try simp only [erase_62 ops other, erase_64 ops other]; all_goals rfl)
#print axioms erase_65

/-- Full symbolic source-function equality for `aspis_core.state_only_hiding.StateOnlyHidingContext.Insts.CoreCmpPartialEqStateOnlyHidingContext`. -/
theorem erase_66 (ops other : ExternalFuns) :
    @aspis_core.state_only_hiding.StateOnlyHidingContext.Insts.CoreCmpPartialEqStateOnlyHidingContext _ (replace ops other) = @aspis_core.state_only_hiding.StateOnlyHidingContext.Insts.CoreCmpPartialEqStateOnlyHidingContext _ ops := by
  delta aspis_core.state_only_hiding.StateOnlyHidingContext.Insts.CoreCmpPartialEqStateOnlyHidingContext
  all_goals rfl
#print axioms erase_66

/-- Full symbolic source-function equality for `aspis_prover.state_only_entropy.ReservedStateOnlyAttemptSecrets.validate_pool_v1_context`. -/
theorem erase_67 (ops other : ExternalFuns) :
    @aspis_prover.state_only_entropy.ReservedStateOnlyAttemptSecrets.validate_pool_v1_context _ (replace ops other) = @aspis_prover.state_only_entropy.ReservedStateOnlyAttemptSecrets.validate_pool_v1_context _ ops := by
  delta aspis_prover.state_only_entropy.ReservedStateOnlyAttemptSecrets.validate_pool_v1_context
  first | rfl | (try simp only [erase_66 ops other]; all_goals rfl)
#print axioms erase_67

/-- Full symbolic source-function equality for `aspis_prover.state_only_entropy.source_inactive_step`. -/
theorem erase_68 (ops other : ExternalFuns) :
    @aspis_prover.state_only_entropy.source_inactive_step _ (replace ops other) = @aspis_prover.state_only_entropy.source_inactive_step _ ops := by
  delta aspis_prover.state_only_entropy.source_inactive_step
  all_goals rfl
#print axioms erase_68

/-- Full symbolic source-function equality for `aspis_prover.state_only_entropy.source_inactive_sum_loop.body`. -/
theorem erase_69 (ops other : ExternalFuns) :
    @aspis_prover.state_only_entropy.source_inactive_sum_loop.body _ (replace ops other) = @aspis_prover.state_only_entropy.source_inactive_sum_loop.body _ ops := by
  delta aspis_prover.state_only_entropy.source_inactive_sum_loop.body
  first | rfl | (try simp only [erase_68 ops other]; all_goals rfl)
#print axioms erase_69

/-- Full symbolic source-function equality for `aspis_prover.state_only_entropy.source_inactive_sum_loop`. -/
theorem erase_70 (ops other : ExternalFuns) :
    @aspis_prover.state_only_entropy.source_inactive_sum_loop _ (replace ops other) = @aspis_prover.state_only_entropy.source_inactive_sum_loop _ ops := by
  delta aspis_prover.state_only_entropy.source_inactive_sum_loop
  first | rfl | (try simp only [erase_69 ops other]; all_goals rfl)
#print axioms erase_70

/-- Full symbolic source-function equality for `aspis_prover.state_only_entropy.source_inactive_sum`. -/
theorem erase_71 (ops other : ExternalFuns) :
    @aspis_prover.state_only_entropy.source_inactive_sum _ (replace ops other) = @aspis_prover.state_only_entropy.source_inactive_sum _ ops := by
  delta aspis_prover.state_only_entropy.source_inactive_sum
  first | rfl | (try simp only [erase_70 ops other]; all_goals rfl)
#print axioms erase_71

/-- Full symbolic source-function equality for `aspis_prover.state_only_entropy.balance_source_d`. -/
theorem erase_72 (ops other : ExternalFuns) :
    @aspis_prover.state_only_entropy.balance_source_d _ (replace ops other) = @aspis_prover.state_only_entropy.balance_source_d _ ops := by
  delta aspis_prover.state_only_entropy.balance_source_d
  first | rfl | (try simp only [erase_71 ops other]; all_goals rfl)
#print axioms erase_72

/-- Full symbolic source-function equality for `aspis_prover.state_only_entropy.pool_v1_private_attempt_binding`. -/
theorem erase_73 (ops other : ExternalFuns) :
    @aspis_prover.state_only_entropy.pool_v1_private_attempt_binding _ (replace ops other) = @aspis_prover.state_only_entropy.pool_v1_private_attempt_binding _ ops := by
  delta aspis_prover.state_only_entropy.pool_v1_private_attempt_binding
  all_goals rfl
#print axioms erase_73

/-- Full symbolic source-function equality for `aspis_prover.state_only_entropy.Profile21SourceExpander.next_word`. -/
theorem erase_74 (ops other : ExternalFuns) :
    @aspis_prover.state_only_entropy.Profile21SourceExpander.next_word _ (replace ops other) = @aspis_prover.state_only_entropy.Profile21SourceExpander.next_word _ ops := by
  delta aspis_prover.state_only_entropy.Profile21SourceExpander.next_word
  first | rfl | (try simp only [erase_62 ops other, erase_64 ops other]; all_goals rfl)
#print axioms erase_74

/-- Full symbolic source-function equality for `aspis_prover.state_only_entropy.Profile21SourceExpander.m31_loop.body`. -/
theorem erase_75 (ops other : ExternalFuns) :
    @aspis_prover.state_only_entropy.Profile21SourceExpander.m31_loop.body _ (replace ops other) = @aspis_prover.state_only_entropy.Profile21SourceExpander.m31_loop.body _ ops := by
  delta aspis_prover.state_only_entropy.Profile21SourceExpander.m31_loop.body
  first | rfl | (try simp only [erase_74 ops other]; all_goals rfl)
#print axioms erase_75

/-- Full symbolic source-function equality for `aspis_prover.state_only_entropy.Profile21SourceExpander.m31_loop`. -/
theorem erase_76 (ops other : ExternalFuns) :
    @aspis_prover.state_only_entropy.Profile21SourceExpander.m31_loop _ (replace ops other) = @aspis_prover.state_only_entropy.Profile21SourceExpander.m31_loop _ ops := by
  delta aspis_prover.state_only_entropy.Profile21SourceExpander.m31_loop
  first | rfl | (try simp only [erase_75 ops other]; all_goals rfl)
#print axioms erase_76

/-- Full symbolic source-function equality for `aspis_prover.state_only_entropy.Profile21SourceExpander.m31`. -/
theorem erase_77 (ops other : ExternalFuns) :
    @aspis_prover.state_only_entropy.Profile21SourceExpander.m31 _ (replace ops other) = @aspis_prover.state_only_entropy.Profile21SourceExpander.m31 _ ops := by
  delta aspis_prover.state_only_entropy.Profile21SourceExpander.m31
  first | rfl | (try simp only [erase_76 ops other]; all_goals rfl)
#print axioms erase_77

/-- Full symbolic source-function equality for `aspis_prover.state_only_entropy.Profile21SourceExpander.qm31`. -/
theorem erase_78 (ops other : ExternalFuns) :
    @aspis_prover.state_only_entropy.Profile21SourceExpander.qm31 _ (replace ops other) = @aspis_prover.state_only_entropy.Profile21SourceExpander.qm31 _ ops := by
  delta aspis_prover.state_only_entropy.Profile21SourceExpander.qm31
  first | rfl | (try simp only [erase_77 ops other]; all_goals rfl)
#print axioms erase_78

/-- Full symbolic source-function equality for `aspis_prover.state_only_entropy.sample_source_d_loop.body`. -/
theorem erase_79 (ops other : ExternalFuns) :
    @aspis_prover.state_only_entropy.sample_source_d_loop.body _ (replace ops other) = @aspis_prover.state_only_entropy.sample_source_d_loop.body _ ops := by
  delta aspis_prover.state_only_entropy.sample_source_d_loop.body
  first | rfl | (try simp only [erase_78 ops other]; all_goals rfl)
#print axioms erase_79
end R1Z.PDict_ReachErase
