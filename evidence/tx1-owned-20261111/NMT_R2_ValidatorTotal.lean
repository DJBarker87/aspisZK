import NMT_R2_ValidatorPayment
set_option autoImplicit false
noncomputable section
namespace NMT_R2_ValidatorTotal
open Aeneas Aeneas.Std NMT_345
attribute [local instance] Classical.propDecidable
abbrev S := NFY_NBN_StatementResult.Statement
abbrev E := AspisR1TerminalDecoder.pool_v1.pair_forest_terminal.PoolV1PairForestTerminalFormatErrorV1

def value (s : S) : core.result.Result Unit E :=
 if (NFY_NBN_StatementResult.common s).master_account = NFY_NBN_StatementResult.zero ∨
    (NFY_NBN_StatementResult.common s).checkpoint_account = NFY_NBN_StatementResult.zero ∨
    (NFY_NBN_StatementResult.common s).selected_lane_account = NFY_NBN_StatementResult.zero then
  .Err .NonZeroBinding
 else if 8 ≤ (NFY_NBN_StatementResult.common s).output_lane.val then .Err .InvalidOutputLane
 else match NMT_R2_ValidatorPayment.value s with
  | .Err e => .Err (.Payment e)
  | .Ok _ => NFY_NBN_StatementResult.suffix s

theorem source (s : S) :
 AspisR1TerminalDecoder.pool_v1.pair_forest_terminal.validate_pool_v1_pair_forest_terminal_statement_v1 s =
 .ok (value s) := by
 rw [NFY_NBN_StatementResult.source]
 unfold NFY_NBN_StatementResult.result value
 dsimp only
 split
 · rfl
 · split
   · rfl
   · rw [NMT_R2_ValidatorPayment.source]
     cases NMT_R2_ValidatorPayment.value s <;> rfl

def fresh (st : Statement) : core.result.Result Unit FormatError :=
 mapCore id NMT_345Dec.fromT13 (value (NMT_345Dec.toT8 st))

theorem emitted (st : Statement) : validateCall st = .ok (fresh st) := by
 unfold validateCall
 rw [source]
 rfl
#print axioms source
#print axioms emitted
end NMT_R2_ValidatorTotal
end
