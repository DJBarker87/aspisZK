import Lean
import NGE_NBN_ResultDependency
import NFY_Part031
import NGE_NEM_EncoderFrame
import NFY_Part032

set_option autoImplicit false
noncomputable section
namespace NGE_NEQ_ResultValidator
open Aeneas Aeneas.Std Result AspisR1TerminalDecoder NFY_NBN_StatementResult
attribute [local instance] Classical.propDecidable
abbrev Record := NGE_NBN_ResultValidator.Record
abbrev Lane := NFY_NEE_ValidatorMutation.Lane
abbrev After := NFY_NEM_LateOracle.After
inductive Call where
  | lane (d : Array U32 8#usize)
  | after (a : NFY_NBH_Validators.Afterstate)

def afterStep (after : After) (r : Record) :
    Result (core.result.Result Unit NFY_NBN_StatementResult.Error) × List Call :=
  let result := do
    let a ← after r.verified_afterstate
    match a with
    | .Err e => ok (.Err (.Afterstate e))
    | .Ok _ => ok (.Ok ())
  (result,[.after r.verified_afterstate])

def run (lane : Lane) (after : After) (r : Record) :
    Result (core.result.Result Unit NFY_NBN_StatementResult.Error) × List Call :=
  if r.master_account = zero ∨ r.selected_lane_account = zero then (ok (.Err .NonZeroBinding),[])
  else match lane r.nullifier with
    | .fail e => (.fail e,[.lane r.nullifier])
    | .div => (.div,[.lane r.nullifier])
    | .ok (.Err e) => (ok (.Err (.Account e)),[.lane r.nullifier])
    | .ok (.Ok l) =>
      if r.output_lane ≠ l then (ok (.Err .OutputLaneMismatch),[.lane r.nullifier])
      else ((afterStep after r).1,.lane r.nullifier :: (afterStep after r).2)

def nativeAfter : After := pool_v1.pair_terminal.encode_pool_v1_pair_verified_afterstate_v1

theorem result (r : Record) :
    (run NFY_NEM_LaneReached.lane nativeAfter r).1 =
      pool_v1.pair_forest_terminal.validate_result r := by
  rw [NGE_NBN_ResultValidator.source]
  unfold run afterStep NGE_NBN_ResultValidator.status nativeAfter NFY_NEM_LaneReached.lane
  rw [NFY_NBN_OutputLane.source]
  by_cases h : r.master_account = zero ∨ r.selected_lane_account = zero
  · simp only [h,if_true]
  · simp only [h,if_false]
    cases hl : NFY_NBN_OutputLane.result r.nullifier with
    | Err e => rfl
    | Ok l =>
      dsimp only
      by_cases mismatch : r.output_lane ≠ l
      · simp only [if_pos mismatch]
      · simp only [if_neg mismatch]
        rw [NFY_NBK_AfterstateResult.source]
        cases ha : NFY_NBH_Validators.afterResult r.verified_afterstate <;> rfl

theorem call_shape (lane : Lane) (after : After) (r : Record) :
    (run lane after r).2 = [] ∨
    (run lane after r).2 = [.lane r.nullifier] ∨
    (run lane after r).2 = [.lane r.nullifier,.after r.verified_afterstate] := by
  unfold run
  split
  · exact Or.inl rfl
  · cases h : lane r.nullifier with
    | fail e => exact Or.inr (Or.inl rfl)
    | div => exact Or.inr (Or.inl rfl)
    | ok status => cases status with
      | Err e => exact Or.inr (Or.inl rfl)
      | Ok l =>
        dsimp only
        by_cases mismatch : r.output_lane ≠ l
        · simp only [if_pos mismatch,or_true,true_or]
        · try simp only [if_neg mismatch]
          exact Or.inr (Or.inr rfl)

theorem lane_domain (lane : Lane) (after : After) (r : Record) (d : Array U32 8#usize)
    (reached : Call.lane d ∈ (run lane after r).2) : d=r.nullifier := by
  rcases call_shape lane after r with a | b | c <;>
    simp_all only [List.mem_cons,List.not_mem_nil,reduceCtorEq,false_or,or_false,Call.lane.injEq]

theorem after_domain (lane : Lane) (after : After) (r : Record) (a : NFY_NBH_Validators.Afterstate)
    (reached : Call.after a ∈ (run lane after r).2) : a=r.verified_afterstate := by
  rcases call_shape lane after r with x | y | z <;>
    simp_all only [List.mem_cons,List.not_mem_nil,reduceCtorEq,false_or,or_false,Call.after.injEq]

def effects (r : Record) : List Call :=
  if r.master_account = zero ∨ r.selected_lane_account = zero then []
  else match NFY_NBN_OutputLane.result r.nullifier with
    | .Err _ => [.lane r.nullifier]
    | .Ok l => if r.output_lane ≠ l then [.lane r.nullifier]
      else [.lane r.nullifier,.after r.verified_afterstate]

theorem ordered_effects (r : Record) :
    (run NFY_NEM_LaneReached.lane nativeAfter r).2 = effects r := by
  unfold run effects NFY_NEM_LaneReached.lane
  rw [NFY_NBN_OutputLane.source]
  by_cases h : r.master_account = zero ∨ r.selected_lane_account = zero
  · simp only [h,if_true]
  · simp only [h,if_false]
    cases NFY_NBN_OutputLane.result r.nullifier with
    | Err e => rfl
    | Ok l =>
      dsimp only
      by_cases mismatch : r.output_lane ≠ l
      · simp only [if_pos mismatch]
      · simp only [if_neg mismatch];rfl

theorem result_state_effects {State : Type} (r : Record) (state : State) :
    let observed := run NFY_NEM_LaneReached.lane nativeAfter r
    (observed.1,state,observed.2) =
      (pool_v1.pair_forest_terminal.validate_result r,state,effects r) := by
  dsimp only
  rw [result,ordered_effects]

#print axioms result
#print axioms call_shape
#print axioms lane_domain
#print axioms after_domain
#print axioms ordered_effects
#print axioms result_state_effects
end NGE_NEQ_ResultValidator

run_cmd do
 let env ← Lean.getEnv
 env.constants.toList.forM fun (n, ci) => do
  if ci.isTheorem && (env.getModuleIdxFor? n).isNone then
   Lean.Elab.Command.elabCommand (← `(command| #print axioms $(Lean.mkIdent n)))
