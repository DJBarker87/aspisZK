import Lean
import NGF_NEX_StatementExt

set_option autoImplicit false
noncomputable section
namespace NGF_NEY_Field07
open Aeneas Aeneas.Std
open AspisR1TerminalDecoder.pool_v1.pair_forest_terminal
abbrev Statement := PoolV1PairForestTerminalStatementV1

def expected (s : Statement) (i : Fin 8) (j : Fin 32) (k : Fin 20) : Nat :=
 match s with
 | .PrivateTransfer c p => (NFY_NEU_PublicProjections.get c.lane_transition.live_snapshot.pool j).val
 | .Withdrawal c p => (NFY_NEU_PublicProjections.get c.lane_transition.live_snapshot.pool j).val

/-- The observed frozen native field has this exact cohort coordinate. The
complete-record extensionality theorem is imported, never re-proved. -/
theorem alignment (s : Statement) (i : Fin 8) (j : Fin 32) (k : Fin 20) :
    NGF_NEX_StatementExt.project s ⟨7,by decide⟩ i j k = expected s i j k := by
  cases s <;> rfl
#print axioms alignment
end NGF_NEY_Field07

run_cmd do
 let env ← Lean.getEnv
 env.constants.toList.forM fun (n, ci) => do
  if ci.isTheorem && (env.getModuleIdxFor? n).isNone then
   Lean.Elab.Command.elabCommand (← `(command| #print axioms $(Lean.mkIdent n)))
