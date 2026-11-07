import NMT_345ReadonlyPublic
set_option autoImplicit false
noncomputable section
namespace NMT_345
open Aeneas Aeneas.Std Result
/-- CLOSED341 at its own exact input domain. The domain is NOT assumed of
345; this theorem is local support awaiting discharge or the std supplement. -/
def checkpointCall {W : Type} (s : Selected W) : Result (core.result.Result Unit PE) :=
 mapOuter (mapCore id fromPE)
  (AdapterRw.r1_pool_adapter.owned.require_verifier_checkpoint
   (NGL_CheckpointModel.install baseOps) (toAccount s.checkpointAccount) s.program true)
def checkpointStep {W : Type} (s : Selected W) (next : Selected W → Result Ret) : Result Ret :=
 tryStep (checkpointCall s) (fun _ => next s)
theorem checkpoint_closed {W : Type} (s : Selected W) (next : Selected W → Result Ret)
 (domain : NGL_LengthCarrier.domain (toAccount s.checkpointAccount).length) :
 checkpointStep s next =
 tryStep (mapOuter (mapCore id fromPE) (.ok
   (NHJ_CheckpointPacket.G (toAccount s.checkpointAccount) s.program true
    (NHJ_CheckpointPacket.encode (toAccount s.checkpointAccount).length)))) (fun _ => next s) := by
 unfold checkpointStep checkpointCall
 rw [NHJ_CheckpointPacket.substitute _ _ _ _ domain]
/-- The existing emitted helper's generic source law, with error.clone
interpreted by the std identity. It keeps arbitrary String errors intact;
it is source/library support, not an expanded native Kani credit. -/
theorem checkpoint_std {W : Type} (s : Selected W) (next : Selected W → Result Ret) :
 checkpointStep s next =
 tryStep (.ok (mapCore id fromPE
   (NGL_CheckpointModel.reply (toAccount s.checkpointAccount) s.program true))) (fun _ => next s) := by
 unfold checkpointStep checkpointCall
 rw [NGL_CheckpointModel.result]
 rfl
#print axioms checkpoint_closed
#print axioms checkpoint_std
end NMT_345
