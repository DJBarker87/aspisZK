import NJI_CheckpointLoop
import NJI_Extracted.Types
set_option autoImplicit false
noncomputable section
namespace NJQ_CheckpointTrace
open Aeneas Aeneas.Std Result NJI_CheckpointLoop
attribute [local instance] Classical.propDecidable
abbrev F := NJI_Extracted.aspis_statement.pool_v1.pair_forest_accounts.PoolV1PairForestAccountErrorV1

/-- Reviewed NJI_K033/K034 one-step clauses, composed by source loop order.
The rejecting step retains its write; it has no recursive suffix. -/
inductive Trace (target : Words) : Nat → Words → core.result.Result Words F → Prop
 | done (state : Words) : Trace target 8 state (.Ok state)
 | reject (k : Nat) (before after : Words) (bound : k<8)
     (frame : Frame before after target k) (bad : NHY_ArrayExt.coord target k>capacity) :
     Trace target k before (.Err .InvalidMasterState)
 | step (k : Nat) (before after : Words) (out : core.result.Result Words F) (bound : k<8)
     (frame : Frame before after target k) (good : NHY_ArrayExt.coord target k≤capacity)
     (tail : Trace target (k+1) after out) : Trace target k before out

/-- All eight clauses, with no successful-loop premise or output equality. -/
theorem result {target before : Words} {k : Nat} {out : core.result.Result Words F}
 (trace : Trace target k before out) :
 NHY_ArrayExt.Prefix before target k → ValidPrefix before k →
 out=(if ∀ j,j<8 → NHY_ArrayExt.coord target j≤capacity then .Ok target else .Err .InvalidMasterState) := by
 induction trace with
 | done state =>
   intro pre valid
   have same := NJI_CheckpointLoop.finished state target pre
   subst state
   have all : ∀ j,j<8 → NHY_ArrayExt.coord target j≤capacity := by
    intro j hj;exact valid j hj hj
   simp only [if_pos all]
 | reject k before after bound frame bad =>
   intro _ _
   have notAll : ¬(∀ j,j<8 → NHY_ArrayExt.coord target j≤capacity) := by
    intro all;exact (not_le.mpr bad) (all k bound)
   simp only [if_neg notAll]
 | step k before after out bound frame good tail ih =>
   intro pre valid
   exact ih (NJI_CheckpointLoop.written_step before after target k bound pre frame)
     (NJI_CheckpointLoop.valid_step before after target k valid frame good)

theorem initial (target : Words) (out : core.result.Result Words F)
 (trace : Trace target 0 (Array.repeat 8#usize 0#u64) out) :
 out=(if ∀ j,j<8 → NHY_ArrayExt.coord target j≤capacity then .Ok target else .Err .InvalidMasterState) := by
 apply result trace
 · intro j hj;omega
 · intro j hj;omega

#print initial
#print axioms result
#print axioms initial
end NJQ_CheckpointTrace
