import Lean
import NFY_Part029

set_option autoImplicit false
noncomputable section
namespace NGE_NEM_KindInstance
open Aeneas Aeneas.Std Result AspisR1TerminalDecoder NFY_NBN_StatementResult

def write (before : Nat → U8) (value : U8) (j : Nat) : U8 :=
  if j=5 then value else before j

/-- Actual enclosing encoder's SAME variant tag, with the complete scalar-write frame. -/
theorem statement_window (s : Statement) (before : Nat → U8) (j : Nat) :
    write before (NFY_NBN_EncoderBytes.tag s) j =
      if j=5 then (match s with | .PrivateTransfer _ _ => 1#u8 | .Withdrawal _ _ => 2#u8)
      else before j := by
  rw [NFY_NBN_U05.encoder_kind]
  rfl

/-- A payment carrier keeps its SAME public value and variant when joined to any common carrier. -/
def join (c : NBD_TerminalProjection.Common)
    (p : Sum NFY_NBN_ValidatorSummary.Transfer NFY_NBN_ValidatorSummary.Withdrawal) : Statement :=
  match p with | .inl t => .PrivateTransfer c t | .inr w => .Withdrawal c w

theorem payment_window (c : NBD_TerminalProjection.Common)
    (p : Sum NFY_NBN_ValidatorSummary.Transfer NFY_NBN_ValidatorSummary.Withdrawal)
    (before : Nat → U8) (j : Nat) :
    write before (NFY_NBN_EncoderBytes.tag (join c p)) j =
      if j=5 then (match p with | .inl _ => 1#u8 | .inr _ => 2#u8) else before j := by
  cases p <;> exact statement_window _ before j

/-- The caller supplies this SAME header byte. Both valid and every invalid byte preserve state. -/
theorem parser_result_frame {State : Type} (header : Nat → U8) (state : State) :
    (pool_v1.pair_forest_terminal.transition_kind (header 5),state) =
      (ok (NBD_TerminalProjection.kind (header 5)),state) := by
  rw [NBD_TerminalProjection.source_kind]

#print axioms statement_window
#print axioms payment_window
#print axioms parser_result_frame
end NGE_NEM_KindInstance

run_cmd do
 let env ← Lean.getEnv
 env.constants.toList.forM fun (n, ci) => do
  if ci.isTheorem && (env.getModuleIdxFor? n).isNone then
   Lean.Elab.Command.elabCommand (← `(command| #print axioms $(Lean.mkIdent n)))
