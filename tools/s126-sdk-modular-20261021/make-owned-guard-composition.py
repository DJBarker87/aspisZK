#!/usr/bin/env python3
from pathlib import Path
R=Path(__file__).resolve().parents[2];S=R/'docs/research/100bit-spend-path-20261013/lean-candidates/s126-caller-boundary-20261021'
s=(S/'S2OwnedSourceInstallationV1.lean').read_text();a=s.index('theorem tail_current_first');b=s.index(' := by',a)
statement=s[a:b].replace('theorem tail_current_first','theorem guarded_current_first').replace('(checkpointIn data checkpointOut : Slice U8)', '(checkpoint : alloc.vec.Vec U8) (data checkpointOut : Slice U8)').replace('owned_stage1_tail (install ops verifierOps) checkpointIn data', 'afterCheckpointBorrow ops verifierOps checkpoint data').replace('checkpointIn','(alloc.vec.Vec.deref checkpoint)')
statement=statement.replace('    ∃ (publicData', '    (∀ byte ∈ checkpoint.val, byte = 0#u8) ∧\n    ∃ (publicData')
out='''import S2OwnedSourceInstallationV1
import S2CheckpointGuardTransportV1
set_option autoImplicit false
noncomputable section
open Aeneas Aeneas.Std Result
namespace AspisS2OwnedStage1.SourceInstallation

/-- Composition of the concrete emitted owned scan and installed owned tail.
This names the reference at the checkpoint-borrow cut. It does not assert the
unproved SDK wrapper/owned reference correspondence. The ordered IO children
are evaluated only after the scan accepts, at their original tail positions. -/
def afterCheckpointBorrow (ops : Ops) (verifierOps : AspisR1CurrentCaller.Ops)
    (checkpoint : alloc.vec.Vec U8) (data : Slice U8) :
    Result (core.result.Result Unit solana_program_error.ProgramError × Slice U8) := do
  let nonzero ← owned_checkpoint_nonzero checkpoint
  if nonzero then
    ok (.Err solana_program_error.ProgramError.AccountAlreadyInitialized,
      alloc.vec.Vec.deref checkpoint)
  else owned_stage1_tail (install ops verifierOps) (alloc.vec.Vec.deref checkpoint) data

/-- Reject branch, complete Result and unchanged bytes. No public/proof read,
decoder, verifier, or checkpoint write is evaluated on this branch. -/
theorem nonzero_reject (ops : Ops) (verifierOps : AspisR1CurrentCaller.Ops)
    (checkpoint : alloc.vec.Vec U8) (data : Slice U8)
    (h : CheckpointGuardTransport.stdAny checkpoint.val = true) :
    afterCheckpointBorrow ops verifierOps checkpoint data =
      ok (.Err solana_program_error.ProgramError.AccountAlreadyInitialized,
        alloc.vec.Vec.deref checkpoint) := by
  unfold afterCheckpointBorrow
  rw [CheckpointGuardTransport.owned_eq_std, h]
  rfl

/-- ACCEPTED-ONLY enclosing reference theorem. The zero-buffer and successful
scan premises are removed: both follow from the same guarded execution. The
actual SDK read/borrow interpretation is still explicitly uninstantiated. -/
'''+statement+''' := by
  unfold afterCheckpointBorrow at h
  rw [CheckpointGuardTransport.owned_eq_std] at h
  cases hs : CheckpointGuardTransport.stdAny checkpoint.val with
  | true => simp only [hs,bind_tc_ok,Bool.true_eq,if_true] at h; cases h
  | false =>
    simp only [hs,bind_tc_ok,Bool.false_eq_true,if_false] at h
    exact ⟨(CheckpointGuardTransport.stdAny_false checkpoint.val).mp hs,
      tail_current_first ops verifierOps (alloc.vec.Vec.deref checkpoint) data checkpointOut h⟩

#print axioms nonzero_reject
#print axioms guarded_current_first
end AspisS2OwnedStage1.SourceInstallation
'''
(S/'S2OwnedGuardCompositionV1.lean').write_text(out)
