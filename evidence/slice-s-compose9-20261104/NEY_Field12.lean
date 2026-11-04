import NEX_StatementExt
set_option autoImplicit false
noncomputable section
namespace NEY_Field12
open Aeneas Aeneas.Std
open AspisR1TerminalDecoder.pool_v1.pair_forest_terminal
abbrev Statement := PoolV1PairForestTerminalStatementV1

def expected (s : Statement) (i : Fin 8) (j : Fin 32) (k : Fin 20) : Nat :=
 match s with
 | .PrivateTransfer c p => (NEU_PublicProjections.get (NEU_PublicProjections.get c.lane_transition.live_snapshot.frontier k) i).val
 | .Withdrawal c p => (NEU_PublicProjections.get (NEU_PublicProjections.get c.lane_transition.live_snapshot.frontier k) i).val

/-- The observed frozen native field has this exact cohort coordinate. The
complete-record extensionality theorem is imported, never re-proved. -/
theorem alignment (s : Statement) (i : Fin 8) (j : Fin 32) (k : Fin 20) :
    NEX_StatementExt.project s ⟨12,by decide⟩ i j k = expected s i j k := by
  cases s <;> rfl
#print axioms alignment
end NEY_Field12
