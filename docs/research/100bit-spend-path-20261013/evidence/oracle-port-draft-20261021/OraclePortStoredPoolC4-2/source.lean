import OraclePortStoredExperimentC4
import OraclePortPool

/-! Logical Pool carrier extension: retain stored bytes with the saved-ten
checkpoint. The finite-support codec is logical, not the frozen account ABI. -/
set_option autoImplicit false
noncomputable section
namespace AspisR1.OraclePortStoredPoolC4
open FS FS2
open AspisV8R19.DuplexFrames AspisV8R19.SourceDuplexStep
open AspisV8R19.MemoizedProgramLaw AspisV8R19.OracleProgramOps
open OraclePortStoredExperimentC4
attribute [local instance] Classical.propDecidable

structure Raw where
  stored : Bytes
  legacy : R9PoolSavedTenModel.Raw

structure Checkpoint where
  stored : Bytes
  legacy : R9PoolSavedTenModel.Checkpoint

/-- Record the prover before projecting away the additional input, so its
oracle calls remain in the recovered commitment-cut log. -/
def prepare (D : LiteralByteProtocol.Decoder) (P : Prover) : Program Bytes State Raw :=
  bind (OracleProgramRecording.record P) fun pv =>
    bind (OracleProgramRecording.record (R9PoolSavedTenModel.rounds D pv.2.proof 33
      (FS.emptyPrefix pv.2.statement))) fun rv =>
        .done ⟨pv.2.stored,(pv.1 ++ rv.1,((pv.2.statement,pv.2.proof),rv.2))⟩

def write (raw : Raw) : Option Checkpoint :=
  (R9PoolSavedTenModel.write raw.legacy).map (fun c => ⟨raw.stored,c⟩)

def stage1 (D : LiteralByteProtocol.Decoder) (P : Prover) :=
  bind (prepare D P) fun raw => .done (write raw)

def embed (stored : Bytes) (v : RawCutProverCompiler.RunView) : RunView :=
  (v.1,(⟨v.2.1.1,v.2.1.2,stored⟩,v.2.2))

def resume (D : LiteralByteProtocol.Decoder) (d : Decision) (c : Checkpoint) :
    Program Bytes State RunView :=
  bind (OraclePortCheckpoint.resume D (d c.stored) c.legacy) fun v =>
    .done (embed c.stored v)

theorem prepare_stored (D : LiteralByteProtocol.Decoder) (P : Prover) (H : Bytes → State) :
    (eval H (prepare D P)).2.stored = (eval H P).2.stored := by
  simp only [prepare,eval_bind,OracleProgramRecording.eval_record,eval]

theorem write_fields (raw : Raw) (c : Checkpoint) (h : write raw = some c) :
    c.stored = raw.stored ∧ c.legacy.raw = raw.legacy := by
  unfold write at h
  cases hw : R9PoolSavedTenModel.write raw.legacy with
  | none => simp only [hw,Option.map_none,reduceCtorEq] at h
  | some old =>
    simp only [hw,Option.map_some,Option.some.injEq] at h
    subst c
    exact ⟨rfl,R9PoolSavedTenModel.write_raw _ _ hw⟩

theorem stage1_stored (D : LiteralByteProtocol.Decoder) (P : Prover) (H : Bytes → State)
    (c : Checkpoint) (h : (eval H (stage1 D P)).2 = some c) :
    c.stored = (eval H P).2.stored := by
  simp only [stage1,eval_bind,eval] at h
  exact (write_fields _ _ h).1.trans (prepare_stored D P H)

theorem resume_stored (D : LiteralByteProtocol.Decoder) (d : Decision) (H : Bytes → State)
    (c : Checkpoint) : (eval H (resume D d c)).2.2.1.stored = c.stored := by
  simp only [resume,eval_bind,eval,embed]

/-- Persisting this packet is lossless, including the full proof bytes.
The proof uses symbolic finite support; it never evaluates the state space. -/
theorem persisted_output (D : LiteralByteProtocol.Decoder) (P : Prover) (H : Bytes → State) :
    R9PoolCheckpointCodec.decode (stage1 D P)
      (R9PoolCheckpointCodec.encode (stage1 D P) (eval H (stage1 D P)).2) =
      some (eval H (stage1 D P)).2 :=
  R9PoolCheckpointCodec.persisted_output _ _

/-- The existing checkpoint matching law survives the added carrier. This is
R15's logical matching law, not the full physical accumulator encoding. -/
theorem resume_matching (D : LiteralByteProtocol.Decoder) (d : Decision)
    (H : Bytes → State) (raw : Raw) (c : Checkpoint)
    (hw : write raw = some c) (ha : (eval H (resume D d c)).2.2.2 = true) :
    c.legacy.saved.next = 10 ∧ ∀ j,
      MatchingSupport.match0 c.legacy.saved.data (c.legacy.saved.queries j) := by
  have old : R9PoolSavedTenModel.write raw.legacy = some c.legacy := by
    unfold write at hw
    cases h : R9PoolSavedTenModel.write raw.legacy with
    | none => simp only [h,Option.map_none,reduceCtorEq] at hw
    | some old =>
      simp only [h,Option.map_some,Option.some.injEq] at hw
      subst c
      rfl
  apply OraclePortCheckpoint.resume_matching D (d c.stored) raw.legacy c.legacy H old
  simpa only [resume,eval_bind,eval,embed] using ha

#print axioms prepare_stored
#print axioms write_fields
#print axioms stage1_stored
#print axioms resume_stored
#print axioms persisted_output
#print axioms resume_matching
end AspisR1.OraclePortStoredPoolC4
end
