import R1Z.PDict_Static222_22A
set_option autoImplicit false
noncomputable section
namespace R1Z.PDict_Static222
open Aeneas Aeneas.Std ProverRwFull PDict_FormatterTypeMaps PDict_FormatterDictionaryMap
/-- Carrier transport candidate for `prover.folded_leaves_loop0.body`. -/
theorem erase_358 (base : ExternalTypes) (F : Type) (ops : @ExternalFuns base) :
    @prover.folded_leaves_loop0.body (types base F) (selected base F ops) = @prover.folded_leaves_loop0.body base ops := by
  delta prover.folded_leaves_loop0.body
  try simp only [erase_357 base F ops]
  all_goals rfl
#print axioms erase_358

/-- Carrier transport candidate for `prover.folded_leaves_loop0`. -/
theorem erase_359 (base : ExternalTypes) (F : Type) (ops : @ExternalFuns base) :
    @prover.folded_leaves_loop0 (types base F) (selected base F ops) = @prover.folded_leaves_loop0 base ops := by
  delta prover.folded_leaves_loop0
  try simp only [erase_358 base F ops]
  all_goals rfl
#print axioms erase_359

/-- Carrier transport candidate for `prover.folded_leaves`. -/
theorem erase_360 (base : ExternalTypes) (F : Type) (ops : @ExternalFuns base) :
    @prover.folded_leaves (types base F) (selected base F ops) = @prover.folded_leaves base ops := by
  delta prover.folded_leaves
  try simp only [erase_359 base F ops]
  all_goals rfl
#print axioms erase_360

/-- Carrier transport candidate for `transport.Variant.Insts.CoreCmpPartialEqVariant`. -/
theorem erase_361 (base : ExternalTypes) (F : Type) (ops : @ExternalFuns base) :
    @transport.Variant.Insts.CoreCmpPartialEqVariant (types base F) (selected base F ops) = @transport.Variant.Insts.CoreCmpPartialEqVariant base ops := by
  delta transport.Variant.Insts.CoreCmpPartialEqVariant
  all_goals rfl
#print axioms erase_361

/-- Carrier transport candidate for `prover.public_check`. -/
theorem erase_362 (base : ExternalTypes) (F : Type) (ops : @ExternalFuns base) :
    @prover.public_check (types base F) (selected base F ops) = @prover.public_check base ops := by
  have hc (c : aspis_z4b_probe.probe.z9.z9b.z9c.z9d.z9e.R1PublicChallenges) :
      @aspis_z4b_probe.probe.z9.z9b.z9c.z9d.z9e.p_r1_check (types base F) (selected base F ops) c =
      resultMap (fun r => (r.1, times base F r.2))
        (@aspis_z4b_probe.probe.z9.z9b.z9c.z9d.z9e.p_r1_check base ops c) := rfl
  delta prover.public_check
  simp only [erase_361 base F ops, hc, PDict_ResultTransport.bind_map, Aeneas.Std.uncurry]
  all_goals rfl
#print axioms erase_362

/-- Carrier transport candidate for `prover.round_loop0_loop0_loop0.body`. -/
theorem erase_363 (base : ExternalTypes) (F : Type) (ops : @ExternalFuns base) :
    @prover.round_loop0_loop0_loop0.body (types base F) (selected base F ops) = @prover.round_loop0_loop0_loop0.body base ops := by
  delta prover.round_loop0_loop0_loop0.body
  all_goals rfl
#print axioms erase_363

/-- Carrier transport candidate for `prover.round_loop0_loop0_loop0`. -/
theorem erase_364 (base : ExternalTypes) (F : Type) (ops : @ExternalFuns base) :
    @prover.round_loop0_loop0_loop0 (types base F) (selected base F ops) = @prover.round_loop0_loop0_loop0 base ops := by
  delta prover.round_loop0_loop0_loop0
  try simp only [erase_363 base F ops]
  all_goals rfl
#print axioms erase_364

/-- Carrier transport candidate for `prover.round_loop0_loop0.body`. -/
theorem erase_365 (base : ExternalTypes) (F : Type) (ops : @ExternalFuns base) :
    @prover.round_loop0_loop0.body (types base F) (selected base F ops) = @prover.round_loop0_loop0.body base ops := by
  delta prover.round_loop0_loop0.body
  try simp only [erase_364 base F ops]
  all_goals rfl
#print axioms erase_365

/-- Carrier transport candidate for `prover.round_loop0_loop0`. -/
theorem erase_366 (base : ExternalTypes) (F : Type) (ops : @ExternalFuns base) :
    @prover.round_loop0_loop0 (types base F) (selected base F ops) = @prover.round_loop0_loop0 base ops := by
  delta prover.round_loop0_loop0
  try simp only [erase_365 base F ops]
  all_goals rfl
#print axioms erase_366

/-- Carrier transport candidate for `prover.round_loop0.body`. -/
theorem erase_367 (base : ExternalTypes) (F : Type) (ops : @ExternalFuns base) :
    @prover.round_loop0.body (types base F) (selected base F ops) = @prover.round_loop0.body base ops := by
  delta prover.round_loop0.body
  try simp only [erase_366 base F ops]
  all_goals rfl
#print axioms erase_367
end R1Z.PDict_Static222
