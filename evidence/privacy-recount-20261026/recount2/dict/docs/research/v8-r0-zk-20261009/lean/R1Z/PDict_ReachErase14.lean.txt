import R1Z.PDict_ReachErase13
set_option autoImplicit false
noncomputable section
namespace R1Z.PDict_ReachErase
open Aeneas Aeneas.Std ProverRwFull
variable [ExternalTypes]
universe u
/-- Equality of the symbolic functionals suffices; no fixed-point unfolding. -/
theorem fixed_equal {α : Type u} [Lean.Order.CCPO α]
    {f g : α → α} (hf : Lean.Order.monotone f) (hg : Lean.Order.monotone g)
    (h : f = g) : Lean.Order.fix f hf = Lean.Order.fix g hg := by
  cases h
  rfl
#print axioms fixed_equal

/-- Full symbolic source-function equality for `host_sumcheck.merge_evaluations_loop.body`. -/
theorem erase_224 (ops other : ExternalFuns) :
    @host_sumcheck.merge_evaluations_loop.body _ (replace ops other) = @host_sumcheck.merge_evaluations_loop.body _ ops := by
  delta host_sumcheck.merge_evaluations_loop.body
  all_goals rfl
#print axioms erase_224

/-- Full symbolic source-function equality for `host_sumcheck.merge_evaluations_loop`. -/
theorem erase_225 (ops other : ExternalFuns) :
    @host_sumcheck.merge_evaluations_loop _ (replace ops other) = @host_sumcheck.merge_evaluations_loop _ ops := by
  delta host_sumcheck.merge_evaluations_loop
  try simp only [erase_224 ops other]
  all_goals rfl
#print axioms erase_225

/-- Full symbolic source-function equality for `host_sumcheck.merge_evaluations`. -/
theorem erase_226 (ops other : ExternalFuns) :
    @host_sumcheck.merge_evaluations _ (replace ops other) = @host_sumcheck.merge_evaluations _ ops := by
  delta host_sumcheck.merge_evaluations
  try simp only [erase_225 ops other]
  all_goals rfl
#print axioms erase_226

/-- Full symbolic source-function equality for `host_sumcheck.evaluate_assignment_loop.body`. -/
theorem erase_227 (ops other : ExternalFuns) :
    @host_sumcheck.evaluate_assignment_loop.body _ (replace ops other) = @host_sumcheck.evaluate_assignment_loop.body _ ops := by
  delta host_sumcheck.evaluate_assignment_loop.body
  all_goals rfl
#print axioms erase_227

/-- Full symbolic source-function equality for `host_sumcheck.evaluate_assignment_loop`. -/
theorem erase_228 (ops other : ExternalFuns) :
    @host_sumcheck.evaluate_assignment_loop _ (replace ops other) = @host_sumcheck.evaluate_assignment_loop _ ops := by
  delta host_sumcheck.evaluate_assignment_loop
  try simp only [erase_227 ops other]
  all_goals rfl
#print axioms erase_228

/-- Full symbolic source-function equality for `host_sumcheck.evaluate_assignment`. -/
theorem erase_229 (ops other : ExternalFuns) :
    @host_sumcheck.evaluate_assignment _ (replace ops other) = @host_sumcheck.evaluate_assignment _ ops := by
  delta host_sumcheck.evaluate_assignment
  try simp only [erase_228 ops other]
  all_goals rfl
#print axioms erase_229

/-- Full symbolic source-function equality for `host_sumcheck.prove_sumcheck_round.closure.Insts.CoreOpsFunctionFnTupleUsizeResultQM31Error.call`. -/
theorem erase_230 (ops other : ExternalFuns) :
    @host_sumcheck.prove_sumcheck_round.closure.Insts.CoreOpsFunctionFnTupleUsizeResultQM31Error.call _ (replace ops other) = @host_sumcheck.prove_sumcheck_round.closure.Insts.CoreOpsFunctionFnTupleUsizeResultQM31Error.call _ ops := by
  delta host_sumcheck.prove_sumcheck_round.closure.Insts.CoreOpsFunctionFnTupleUsizeResultQM31Error.call
  try simp only [erase_229 ops other]
  all_goals rfl
#print axioms erase_230

/-- Full symbolic source-function equality for `host_sumcheck.prove_sumcheck_round.closure.Insts.CoreOpsFunctionFnMutTupleUsizeResultQM31Error.call_mut`. -/
theorem erase_231 (ops other : ExternalFuns) :
    @host_sumcheck.prove_sumcheck_round.closure.Insts.CoreOpsFunctionFnMutTupleUsizeResultQM31Error.call_mut _ (replace ops other) = @host_sumcheck.prove_sumcheck_round.closure.Insts.CoreOpsFunctionFnMutTupleUsizeResultQM31Error.call_mut _ ops := by
  delta host_sumcheck.prove_sumcheck_round.closure.Insts.CoreOpsFunctionFnMutTupleUsizeResultQM31Error.call_mut
  try simp only [erase_230 ops other]
  all_goals rfl
#print axioms erase_231

/-- Full symbolic source-function equality for `host_sumcheck.prove_sumcheck_round.closure.Insts.CoreOpsFunctionFnOnceTupleUsizeResultQM31Error.call_once`. -/
theorem erase_232 (ops other : ExternalFuns) :
    @host_sumcheck.prove_sumcheck_round.closure.Insts.CoreOpsFunctionFnOnceTupleUsizeResultQM31Error.call_once _ (replace ops other) = @host_sumcheck.prove_sumcheck_round.closure.Insts.CoreOpsFunctionFnOnceTupleUsizeResultQM31Error.call_once _ ops := by
  delta host_sumcheck.prove_sumcheck_round.closure.Insts.CoreOpsFunctionFnOnceTupleUsizeResultQM31Error.call_once
  try simp only [erase_231 ops other]
  all_goals rfl
#print axioms erase_232

/-- Full symbolic source-function equality for `host_sumcheck.prove_sumcheck_round.closure.Insts.CoreOpsFunctionFnOnceTupleUsizeResultQM31Error`. -/
theorem erase_233 (ops other : ExternalFuns) :
    @host_sumcheck.prove_sumcheck_round.closure.Insts.CoreOpsFunctionFnOnceTupleUsizeResultQM31Error _ (replace ops other) = @host_sumcheck.prove_sumcheck_round.closure.Insts.CoreOpsFunctionFnOnceTupleUsizeResultQM31Error _ ops := by
  delta host_sumcheck.prove_sumcheck_round.closure.Insts.CoreOpsFunctionFnOnceTupleUsizeResultQM31Error
  try simp only [erase_232 ops other]
  all_goals rfl
#print axioms erase_233

/-- Full symbolic source-function equality for `host_sumcheck.prove_sumcheck_round.closure.Insts.CoreOpsFunctionFnMutTupleUsizeResultQM31Error`. -/
theorem erase_234 (ops other : ExternalFuns) :
    @host_sumcheck.prove_sumcheck_round.closure.Insts.CoreOpsFunctionFnMutTupleUsizeResultQM31Error _ (replace ops other) = @host_sumcheck.prove_sumcheck_round.closure.Insts.CoreOpsFunctionFnMutTupleUsizeResultQM31Error _ ops := by
  delta host_sumcheck.prove_sumcheck_round.closure.Insts.CoreOpsFunctionFnMutTupleUsizeResultQM31Error
  try simp only [erase_231 ops other, erase_233 ops other]
  all_goals rfl
#print axioms erase_234

/-- Full symbolic source-function equality for `host_sumcheck.prove_sumcheck_round.closure.Insts.CoreOpsFunctionFnTupleUsizeResultQM31Error`. -/
theorem erase_235 (ops other : ExternalFuns) :
    @host_sumcheck.prove_sumcheck_round.closure.Insts.CoreOpsFunctionFnTupleUsizeResultQM31Error _ (replace ops other) = @host_sumcheck.prove_sumcheck_round.closure.Insts.CoreOpsFunctionFnTupleUsizeResultQM31Error _ ops := by
  delta host_sumcheck.prove_sumcheck_round.closure.Insts.CoreOpsFunctionFnTupleUsizeResultQM31Error
  try simp only [erase_234 ops other, erase_230 ops other]
  all_goals rfl
#print axioms erase_235

/-- Full symbolic source-function equality for `host_sumcheck.prove_sumcheck_round`. -/
theorem erase_236 (ops other : ExternalFuns) :
    @host_sumcheck.prove_sumcheck_round _ (replace ops other) = @host_sumcheck.prove_sumcheck_round _ ops := by
  delta host_sumcheck.prove_sumcheck_round
  try simp only [erase_60 ops other, erase_210 ops other, erase_223 ops other, erase_226 ops other, erase_235 ops other, erase_202 ops other, erase_203 ops other]
  all_goals rfl
#print axioms erase_236

/-- Full symbolic source-function equality for `host_sumcheck.prove_sumcheck_rounds`. -/
theorem erase_237 (ops other : ExternalFuns) :
    @host_sumcheck.prove_sumcheck_rounds _ (replace ops other) = @host_sumcheck.prove_sumcheck_rounds _ ops := by
  have hmutual :
      @host_sumcheck.prove_sumcheck_rounds.mutual _ (replace ops other) =
      @host_sumcheck.prove_sumcheck_rounds.mutual _ ops := by
    funext H F digest oracle state
    delta host_sumcheck.prove_sumcheck_rounds.mutual
    apply fixed_equal
    funext recur transcript output point running round
    simp only [erase_60 ops other, erase_236 ops other]
  delta host_sumcheck.prove_sumcheck_rounds
  rw [hmutual]
#print axioms erase_237

/-- Full symbolic source-function equality for `host_sumcheck.prove_sumcheck`. -/
theorem erase_238 (ops other : ExternalFuns) :
    @host_sumcheck.prove_sumcheck _ (replace ops other) = @host_sumcheck.prove_sumcheck _ ops := by
  delta host_sumcheck.prove_sumcheck
  try simp only [erase_237 ops other]
  all_goals rfl
#print axioms erase_238

/-- Full symbolic source-function equality for `host_wire.SemanticTranscript.challenge_reference_circle_point`. -/
theorem erase_239 (ops other : ExternalFuns) :
    @host_wire.SemanticTranscript.challenge_reference_circle_point _ (replace ops other) = @host_wire.SemanticTranscript.challenge_reference_circle_point _ ops := by
  delta host_wire.SemanticTranscript.challenge_reference_circle_point
  try simp only [erase_201 ops other]
  all_goals rfl
#print axioms erase_239
end R1Z.PDict_ReachErase
