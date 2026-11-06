import NJI_CheckpointLoop
set_option autoImplicit false
namespace NJQ_MasterTrace
open Aeneas Aeneas.Std Result NJI_CheckpointLoop
/-- Same local-array frame as checkpoint, without a per-step capacity guard.
Master validates the completed record only after this loop returns. -/
inductive Writes (target : Words) : Nat → Words → Words → Prop
 | done (state : Words) : Writes target 8 state state
 | step (k : Nat) (before after out : Words) (bound : k<8)
   (frame : Frame before after target k) (tail : Writes target (k+1) after out) :
   Writes target k before out

theorem result {target before out : Words} {k : Nat} (trace : Writes target k before out) :
 NHY_ArrayExt.Prefix before target k → out=target := by
 induction trace with
 | done state => intro pre;exact NJI_CheckpointLoop.finished state target pre
 | step k before after out bound frame tail ih =>
   intro pre
   exact ih (NJI_CheckpointLoop.written_step before after target k bound pre frame)

theorem initial (target out : Words)
 (trace : Writes target 0 (Array.repeat 8#usize 0#u64) out) : out=target := by
 apply result trace
 intro j hj;omega

#print axioms result
#print axioms initial
end NJQ_MasterTrace
