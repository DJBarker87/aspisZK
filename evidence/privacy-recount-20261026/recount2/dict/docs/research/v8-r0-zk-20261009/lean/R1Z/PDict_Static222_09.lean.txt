import R1Z.PDict_Static222_08
set_option autoImplicit false
noncomputable section
namespace R1Z.PDict_Static222
open Aeneas Aeneas.Std ProverRwFull PDict_FormatterTypeMaps PDict_FormatterDictionaryMap
/-- Carrier transport candidate for `aspis_prover.state_only_hiding.h1_padding_inactive_sum_loop.body`. -/
theorem erase_144 (base : ExternalTypes) (F : Type) (ops : @ExternalFuns base) :
    @aspis_prover.state_only_hiding.h1_padding_inactive_sum_loop.body (types base F) (selected base F ops) = @aspis_prover.state_only_hiding.h1_padding_inactive_sum_loop.body base ops := by
  delta aspis_prover.state_only_hiding.h1_padding_inactive_sum_loop.body
  try simp only [erase_143 base F ops]
  all_goals rfl
#print axioms erase_144

/-- Carrier transport candidate for `aspis_prover.state_only_hiding.h1_padding_inactive_sum_loop`. -/
theorem erase_145 (base : ExternalTypes) (F : Type) (ops : @ExternalFuns base) :
    @aspis_prover.state_only_hiding.h1_padding_inactive_sum_loop (types base F) (selected base F ops) = @aspis_prover.state_only_hiding.h1_padding_inactive_sum_loop base ops := by
  delta aspis_prover.state_only_hiding.h1_padding_inactive_sum_loop
  try simp only [erase_144 base F ops]
  all_goals rfl
#print axioms erase_145

/-- Carrier transport candidate for `aspis_prover.state_only_hiding.h1_padding_inactive_sum`. -/
theorem erase_146 (base : ExternalTypes) (F : Type) (ops : @ExternalFuns base) :
    @aspis_prover.state_only_hiding.h1_padding_inactive_sum (types base F) (selected base F ops) = @aspis_prover.state_only_hiding.h1_padding_inactive_sum base ops := by
  delta aspis_prover.state_only_hiding.h1_padding_inactive_sum
  try simp only [erase_145 base F ops]
  all_goals rfl
#print axioms erase_146

/-- Carrier transport candidate for `aspis_prover.state_only_hiding.apply_h1_padding_mask_for_active`. -/
theorem erase_147 (base : ExternalTypes) (F : Type) (ops : @ExternalFuns base) :
    @aspis_prover.state_only_hiding.apply_h1_padding_mask_for_active (types base F) (selected base F ops) = @aspis_prover.state_only_hiding.apply_h1_padding_mask_for_active base ops := by
  delta aspis_prover.state_only_hiding.apply_h1_padding_mask_for_active
  try simp only [erase_60 base F ops, erase_139 base F ops, erase_142 base F ops, erase_146 base F ops]
  all_goals rfl
#print axioms erase_147

/-- Carrier transport candidate for `aspis_prover.state_only_hiding.apply_pool_v1_pair_forest_h1_padding_mask_v1`. -/
theorem erase_148 (base : ExternalTypes) (F : Type) (ops : @ExternalFuns base) :
    @aspis_prover.state_only_hiding.apply_pool_v1_pair_forest_h1_padding_mask_v1 (types base F) (selected base F ops) = @aspis_prover.state_only_hiding.apply_pool_v1_pair_forest_h1_padding_mask_v1 base ops := by
  delta aspis_prover.state_only_hiding.apply_pool_v1_pair_forest_h1_padding_mask_v1
  try simp only [erase_147 base F ops, erase_106 base F ops]
  all_goals rfl
#print axioms erase_148

/-- Carrier transport candidate for `core.option.Option.Insts.CoreCmpPartialEqOption`. -/
theorem erase_149 (base : ExternalTypes) (F : Type) (ops : @ExternalFuns base) :
    @core.option.Option.Insts.CoreCmpPartialEqOption (types base F) (selected base F ops) = @core.option.Option.Insts.CoreCmpPartialEqOption base ops := by
  delta core.option.Option.Insts.CoreCmpPartialEqOption
  all_goals rfl
#print axioms erase_149

/-- Carrier transport candidate for `host_semantic.claim_mask_value`. -/
theorem erase_150 (base : ExternalTypes) (F : Type) (ops : @ExternalFuns base) :
    @host_semantic.claim_mask_value (types base F) (selected base F ops) = @host_semantic.claim_mask_value base ops := by
  delta host_semantic.claim_mask_value
  try simp only [erase_136 base F ops]
  all_goals rfl
#print axioms erase_150

/-- Carrier transport candidate for `host_semantic.extra_loop0_loop0.body`. -/
theorem erase_151 (base : ExternalTypes) (F : Type) (ops : @ExternalFuns base) :
    @host_semantic.extra_loop0_loop0.body (types base F) (selected base F ops) = @host_semantic.extra_loop0_loop0.body base ops := by
  delta host_semantic.extra_loop0_loop0.body
  all_goals rfl
#print axioms erase_151

/-- Carrier transport candidate for `host_semantic.extra_loop0_loop0`. -/
theorem erase_152 (base : ExternalTypes) (F : Type) (ops : @ExternalFuns base) :
    @host_semantic.extra_loop0_loop0 (types base F) (selected base F ops) = @host_semantic.extra_loop0_loop0 base ops := by
  delta host_semantic.extra_loop0_loop0
  try simp only [erase_151 base F ops]
  all_goals rfl
#print axioms erase_152

/-- Carrier transport candidate for `host_semantic.extra_loop0.body`. -/
theorem erase_153 (base : ExternalTypes) (F : Type) (ops : @ExternalFuns base) :
    @host_semantic.extra_loop0.body (types base F) (selected base F ops) = @host_semantic.extra_loop0.body base ops := by
  delta host_semantic.extra_loop0.body
  try simp only [erase_152 base F ops]
  all_goals rfl
#print axioms erase_153

/-- Carrier transport candidate for `host_semantic.extra_loop0`. -/
theorem erase_154 (base : ExternalTypes) (F : Type) (ops : @ExternalFuns base) :
    @host_semantic.extra_loop0 (types base F) (selected base F ops) = @host_semantic.extra_loop0 base ops := by
  delta host_semantic.extra_loop0
  try simp only [erase_153 base F ops]
  all_goals rfl
#print axioms erase_154

/-- Carrier transport candidate for `host_semantic.extra`. -/
theorem erase_155 (base : ExternalTypes) (F : Type) (ops : @ExternalFuns base) :
    @host_semantic.extra (types base F) (selected base F ops) = @host_semantic.extra base ops := by
  delta host_semantic.extra
  try simp only [erase_154 base F ops]
  all_goals rfl
#print axioms erase_155

/-- Carrier transport candidate for `host_semantic.claims_at_point_loop.body`. -/
theorem erase_156 (base : ExternalTypes) (F : Type) (ops : @ExternalFuns base) :
    @host_semantic.claims_at_point_loop.body (types base F) (selected base F ops) = @host_semantic.claims_at_point_loop.body base ops := by
  delta host_semantic.claims_at_point_loop.body
  all_goals rfl
#print axioms erase_156

/-- Carrier transport candidate for `host_semantic.claims_at_point_loop`. -/
theorem erase_157 (base : ExternalTypes) (F : Type) (ops : @ExternalFuns base) :
    @host_semantic.claims_at_point_loop (types base F) (selected base F ops) = @host_semantic.claims_at_point_loop base ops := by
  delta host_semantic.claims_at_point_loop
  try simp only [erase_156 base F ops]
  all_goals rfl
#print axioms erase_157

/-- Carrier transport candidate for `host_semantic.claims_at_point`. -/
theorem erase_158 (base : ExternalTypes) (F : Type) (ops : @ExternalFuns base) :
    @host_semantic.claims_at_point (types base F) (selected base F ops) = @host_semantic.claims_at_point base ops := by
  delta host_semantic.claims_at_point
  try simp only [erase_157 base F ops]
  all_goals rfl
#print axioms erase_158

/-- Carrier transport candidate for `r1_wire.statement_points`. -/
theorem erase_159 (base : ExternalTypes) (F : Type) (ops : @ExternalFuns base) :
    @r1_wire.statement_points (types base F) (selected base F ops) = @r1_wire.statement_points base ops := by
  delta r1_wire.statement_points
  all_goals rfl
#print axioms erase_159
end R1Z.PDict_Static222
