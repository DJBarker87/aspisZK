import NEX_StatementExt
set_option autoImplicit false
noncomputable section
namespace NEY_Field05
open Aeneas Aeneas.Std
open AspisR1TerminalDecoder.pool_v1.pair_forest_terminal
abbrev Statement := PoolV1PairForestTerminalStatementV1

def expected (s : Statement) (i : Fin 8) (j : Fin 32) (k : Fin 20) : Nat :=
 match s with
 | .PrivateTransfer c p => c.checkpoint_sequence.val
 | .Withdrawal c p => c.checkpoint_sequence.val

/-- The observed frozen native field has this exact cohort coordinate. The
complete-record extensionality theorem is imported, never re-proved. -/
theorem alignment (s : Statement) (i : Fin 8) (j : Fin 32) (k : Fin 20) :
    NEX_StatementExt.project s ⟨5,by decide⟩ i j k = expected s i j k := by
  cases s <;> rfl
#print axioms alignment
end NEY_Field05
