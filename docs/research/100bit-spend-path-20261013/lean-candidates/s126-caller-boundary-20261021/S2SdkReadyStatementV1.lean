import S2SdkReadyBodyV1
set_option autoImplicit false
open Aeneas Aeneas.Std Result
namespace AspisS2OwnedStage1.SdkReference.ReadyStatement
open ReadyState ReadyCaller
abbrev Statement := ReadyBody.Statement
abbrev Common := ReadyBody.Common
abbrev Public := ReadyBody.Public

def commonOf : Statement → Common
  | .PrivateTransfer common _ => common
  | .Withdrawal common _ => common

def publicOf : Statement → Public
  | .PrivateTransfer common pub => .Transfer pub common.lane_transition
  | .Withdrawal common pub => .Withdrawal pub common.lane_transition

/-- TOTAL actual emitted getters: public and encoder inputs come from the
SAME decoded statement, with no independent projection-success premise. -/
theorem common_total (statement : Statement) :
    aspis_statement.pool_v1.pair_forest_terminal.PoolV1PairForestTerminalStatementV1.common statement=
      ok (commonOf statement) := by
  cases statement <;> rfl

theorem public_total (statement : Statement) :
    aspis_statement.pool_v1.pair_forest_terminal.PoolV1PairForestTerminalStatementV1.semantic_public statement=
      ok (publicOf statement) := by
  cases statement <;> rfl

/-- Complete installed reference, same original proof/public vectors, exact
supplied first output in account2, full byte heap effect, unchanged account and
lamport metadata, and its current verifier call with observer None. Whole caller
success and independent common/public witnesses have been removed as premises.
Native SDK observation/representation/oracle/TX2 transport remains separate. -/
theorem construct (ops : Ops) (verifierOps : AspisR1CurrentCaller.Ops)
    (program : Array U8 32#usize) (pa ua ca : OwnedAccount)
    (lamports : alloc.vec.Vec OwnedLamportsCell) (p u c : OwnedDataCell) (ten : Bool)
    (statement : Statement) (candidate : Array U8 688#usize) (checkpointBytes : alloc.vec.Vec U8)
    (distinctPU : pa.key≠ua.key) (distinctPC : pa.key≠ca.key) (distinctUC : ua.key≠ca.key)
    (proofLength : p.bytes.val.length=58295)
    (checkpointLength : c.bytes.val.length=1768)
    (outputLength : checkpointBytes.val.length=1768)
    (proofAllowed : shared_allowed p.borrowed=ok true)
    (publicAllowed : shared_allowed u.borrowed=ok true)
    (scanned : owned_checkpoint_nonzero c.bytes=ok false)
    (decoded : decode_public_statement_box (Installation.install ops verifierOps)
      (alloc.vec.Vec.deref u.bytes)=ok (.Ok statement))
    (validated : (Installation.install ops verifierOps).op5 statement=ok (.Ok ()))
    (encoded : (Installation.install ops verifierOps).op8 (commonOf statement).lane_transition.candidate_afterstate=
      ok (.Ok candidate))
    (compared : (Installation.install ops verifierOps).op0 core.cmp.PartialEqU8
      (FrameOperationsTotal.segment (alloc.vec.Vec.deref p.bytes) 0#usize 688#usize) candidate=ok false)
    (tagRead : alloc.vec.Vec.index (core.slice.index.SliceIndexUsizeSlice U8)
      p.bytes 696#usize=ok 2#u8)
    (firstReturned : first_decoded (Installation.install ops verifierOps) (publicOf statement)
      (alloc.vec.Vec.deref u.bytes)
      (FrameOperationsTotal.segment (alloc.vec.Vec.deref p.bytes) 688#usize 58295#usize)
      (splitIndex ten)=ok (.Ok checkpointBytes)) :
    ∃ out, BorrowedReference.owned_stage1 (Installation.install ops verifierOps)
      program (initialSdk program pa ua ca lamports p u c) (instruction ten)=ok (.Ok (),out) ∧
      ProofGate.FixedLinked.inputBytes (initialSdk program pa ua ca lamports p u c) 0#usize=
        ok (alloc.vec.Vec.deref p.bytes) ∧
      ProofGate.FixedLinked.inputBytes (initialSdk program pa ua ca lamports p u c) 1#usize=
        ok (alloc.vec.Vec.deref u.bytes) ∧
      ProofGate.FixedLinked.inputBytes out 2#usize=ok (alloc.vec.Vec.deref checkpointBytes) ∧
      BorrowedBufferFrame.buffers out=
        (BorrowedBufferFrame.buffers (initialSdk program pa ua ca lamports p u c)).set 2 checkpointBytes ∧
      out.accounts=(initialSdk program pa ua ca lamports p u c).accounts ∧
      out.lamports_cells=lamports ∧
      AspisR1CurrentCaller.verifier.candidate.tx1 verifierOps
        (SourceInstallation.currentDigest
          (SolanaDigest.Insts.Aspis_coreDigestDigest32 (Installation.install ops verifierOps)))
        (CurrentCarrier.toCurrentPublic (publicOf statement)) (alloc.vec.Vec.deref u.bytes)
        (FrameOperationsTotal.segment (alloc.vec.Vec.deref p.bytes) 688#usize 58295#usize)
        (splitIndex ten) () none=ok (.Ok checkpointBytes) := by
  obtain ⟨out,run,saved,image⟩ := ReadyBody.construct ops verifierOps program pa ua ca lamports
    p u c ten statement (commonOf statement) (publicOf statement) candidate checkpointBytes
    distinctPU distinctPC distinctUC proofLength checkpointLength outputLength proofAllowed publicAllowed
    scanned decoded validated (common_total statement) encoded compared tagRead (public_total statement) firstReturned
  have accounts := MetadataFrame.borrowed_accounts_preserved (Installation.install ops verifierOps)
    program (initialSdk program pa ua ca lamports p u c) out (instruction ten) (.Ok ()) run
  have lamportsFrame := MetadataFrame.borrowed_lamports_preserved (Installation.install ops verifierOps)
    program (initialSdk program pa ua ca lamports p u c) out (instruction ten) (.Ok ()) run
  have pAccountRead : alloc.vec.Vec.index (core.slice.index.SliceIndexUsizeSlice OwnedAccount)
      (initialSdk program pa ua ca lamports p u c).accounts 0#usize=ok (readonlyMeta pa 0#usize) := read_zero _ _ _
  have uAccountRead : alloc.vec.Vec.index (core.slice.index.SliceIndexUsizeSlice OwnedAccount)
      (initialSdk program pa ua ca lamports p u c).accounts 1#usize=ok (readonlyMeta ua 1#usize) := read_one _ _ _
  have pCellRead : alloc.vec.Vec.index (core.slice.index.SliceIndexUsizeSlice OwnedDataCell)
      (initialSdk program pa ua ca lamports p u c).data_cells 0#usize=ok p := read_zero _ _ _
  have uCellRead : alloc.vec.Vec.index (core.slice.index.SliceIndexUsizeSlice OwnedDataCell)
      (initialSdk program pa ua ca lamports p u c).data_cells 1#usize=ok u := read_one _ _ _
  have pRead : ProofGate.FixedLinked.inputBytes (initialSdk program pa ua ca lamports p u c) 0#usize=
      ok (alloc.vec.Vec.deref p.bytes) := by
    simp only [ProofGate.FixedLinked.inputBytes,pAccountRead,bind_tc_ok,readonlyMeta,
      BorrowedBufferFrame.readBytes,pCellRead]
  have uRead : ProofGate.FixedLinked.inputBytes (initialSdk program pa ua ca lamports p u c) 1#usize=
      ok (alloc.vec.Vec.deref u.bytes) := by
    simp only [ProofGate.FixedLinked.inputBytes,uAccountRead,bind_tc_ok,readonlyMeta,
      BorrowedBufferFrame.readBytes,uCellRead]
  have cAccountRead : alloc.vec.Vec.index (core.slice.index.SliceIndexUsizeSlice OwnedAccount)
      out.accounts 2#usize=ok (checkpointMeta program ca) := by
    rw [accounts]
    exact read_two _ _ _
  have cRead : ProofGate.FixedLinked.inputBytes out 2#usize=ok (alloc.vec.Vec.deref checkpointBytes) := by
    simp only [ProofGate.FixedLinked.inputBytes,cAccountRead,bind_tc_ok,checkpointMeta,saved]
  refine ⟨out,run,pRead,uRead,cRead,image,accounts,lamportsFrame,?_⟩
  exact Installation.first_success ops verifierOps (publicOf statement) (alloc.vec.Vec.deref u.bytes)
    (FrameOperationsTotal.segment (alloc.vec.Vec.deref p.bytes) 688#usize 58295#usize)
    (splitIndex ten) checkpointBytes firstReturned

#print axioms common_total
#print axioms public_total
#print axioms construct
end AspisS2OwnedStage1.SdkReference.ReadyStatement
