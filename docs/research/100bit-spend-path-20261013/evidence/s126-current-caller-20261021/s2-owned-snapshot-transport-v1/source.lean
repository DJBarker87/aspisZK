import S2OwnedStage1ModelV1
import MultiproofConeVecLaws
set_option autoImplicit false
open Aeneas Aeneas.Std Result
namespace AspisS2OwnedStage1.SnapshotTransport

/-- The landed parser cone proves this for every representable slice length,
not just the SDK checkpoint/public fixture sizes. -/
theorem snapshot_bytes (bytes : Slice U8) :
    alloc.slice.Slice.to_vec core.clone.CloneU8 bytes = ok bytes :=
  AspisR1.MultiproofConeVecLaws.to_vec_bytes bytes

def snapshotRead (read : Result (core.result.Result (Slice U8) solana_program_error.ProgramError)) :
    Result (core.result.Result (alloc.vec.Vec U8) solana_program_error.ProgramError) := do
  let r ← read
  match r with
  | .Err e => ok (.Err e)
  | .Ok bytes =>
    let owned ← alloc.slice.Slice.to_vec core.clone.CloneU8 bytes
    ok (.Ok owned)

/-- TOTAL complete Result transport, preserving SDK errors, failure and
divergence. This is a snapshot theorem, not the missing ordered SDK-read
implementation instance. Guards must stay live at the original program points. -/
theorem snapshotRead_eq (read : Result (core.result.Result (Slice U8) solana_program_error.ProgramError)) :
    snapshotRead read = read := by
  cases read with
  | fail e => rfl
  | div => rfl
  | ok r =>
    cases r with
    | Err e => rfl
    | Ok bytes =>
      simp only [snapshotRead, bind_tc_ok, snapshot_bytes]

def installSnapshots (ops : Ops)
    (publicRead proofRead : Result (core.result.Result (Slice U8) solana_program_error.ProgramError)) : Ops :=
  {ops with op11:=snapshotRead publicRead,op12:=snapshotRead proofRead}

/-- Enclosing owned-tail execution equality with both ordered snapshot
operations supplied; no byte equality or successful-read premise. -/
theorem tail_snapshot_transport (ops : Ops)
    (publicRead proofRead : Result (core.result.Result (Slice U8) solana_program_error.ProgramError))
    (checkpoint data : Slice U8) :
    owned_stage1_tail (installSnapshots ops publicRead proofRead) checkpoint data =
    owned_stage1_tail {ops with op11:=publicRead,op12:=proofRead} checkpoint data := by
  unfold installSnapshots
  rw [snapshotRead_eq, snapshotRead_eq]

#print axioms snapshot_bytes
#print axioms snapshotRead_eq
#print axioms tail_snapshot_transport
end AspisS2OwnedStage1.SnapshotTransport
