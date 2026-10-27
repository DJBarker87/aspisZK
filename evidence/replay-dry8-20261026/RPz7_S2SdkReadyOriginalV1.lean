import RPz7_S2SdkReadyStatementV1
set_option autoImplicit false
open Aeneas Aeneas.Std Result
namespace AspisS2OwnedStage1.SdkReference.ReadyOriginal
open ReadyState ReadyCaller ReadyStatement

theorem readonly_identity (account : OwnedAccount) (slot : Usize)
    (fields : account.is_signer=false ∧ account.is_writable=false ∧ account.executable=false ∧ account.data_slot=slot) :
    readonlyMeta account slot=account := by
  cases account
  simp_all [readonlyMeta]

theorem checkpoint_identity (program : Array U8 32#usize) (account : OwnedAccount)
    (fields : account.owner=program ∧ account.is_signer=false ∧ account.is_writable=true ∧ account.executable=false ∧ account.data_slot=2#usize) :
    checkpointMeta program account=account := by
  cases account
  simp_all [checkpointMeta]

/-- Accepted-native metadata parametrization is an identity on the full
original SDK values. No original byte, owner, flag, rent, slot, counter or Rc
value is silently changed in the enclosing reference constructor. -/
theorem initial_identity (program : Array U8 32#usize) (pa ua ca : OwnedAccount)
    (lamports : alloc.vec.Vec OwnedLamportsCell) (p u c : OwnedDataCell)
    (pMeta : pa.is_signer=false ∧ pa.is_writable=false ∧ pa.executable=false ∧ pa.data_slot=0#usize)
    (uMeta : ua.is_signer=false ∧ ua.is_writable=false ∧ ua.executable=false ∧ ua.data_slot=1#usize)
    (cMeta : ca.owner=program ∧ ca.is_signer=false ∧ ca.is_writable=true ∧ ca.executable=false ∧ ca.data_slot=2#usize)
    (cFree : c.borrowed=0#isize) :
    initialSdk program pa ua ca lamports p u c=state (triple pa ua ca) lamports p u c := by
  have sameCell : {c with borrowed:=0#isize}=c := by
    cases c
    simp_all
  simp only [initialSdk,accounts3,readonly_identity pa 0#usize pMeta,
    readonly_identity ua 1#usize uMeta,checkpoint_identity program ca cMeta,sameCell]

/-- COMPLETE installed caller and saved-output/source-current-first interface,
now on the original three account/data records, without a whole-reference
success or state-equality premise. Guard/child observations remain explicit;
actual SDK representation/accepted-call/oracle/TX2 correspondence is still owed. -/
theorem construct (ops : Ops) (verifierOps : AspisR1CurrentCaller.Ops)
    (program : Array U8 32#usize) (pa ua ca : OwnedAccount)
    (lamports : alloc.vec.Vec OwnedLamportsCell) (p u c : OwnedDataCell) (ten : Bool)
    (statement : Statement) (candidate : Array U8 688#usize) (checkpointBytes : alloc.vec.Vec U8)
    (pMeta : pa.is_signer=false ∧ pa.is_writable=false ∧ pa.executable=false ∧ pa.data_slot=0#usize)
    (uMeta : ua.is_signer=false ∧ ua.is_writable=false ∧ ua.executable=false ∧ ua.data_slot=1#usize)
    (cMeta : ca.owner=program ∧ ca.is_signer=false ∧ ca.is_writable=true ∧ ca.executable=false ∧ ca.data_slot=2#usize)
    (cFree : c.borrowed=0#isize)
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
      program (state (triple pa ua ca) lamports p u c) (instruction ten)=ok (.Ok (),out) ∧
      ProofGate.FixedLinked.inputBytes (state (triple pa ua ca) lamports p u c) 0#usize=
        ok (alloc.vec.Vec.deref p.bytes) ∧
      ProofGate.FixedLinked.inputBytes (state (triple pa ua ca) lamports p u c) 1#usize=
        ok (alloc.vec.Vec.deref u.bytes) ∧
      ProofGate.FixedLinked.inputBytes out 2#usize=ok (alloc.vec.Vec.deref checkpointBytes) ∧
      BorrowedBufferFrame.buffers out=
        (BorrowedBufferFrame.buffers (state (triple pa ua ca) lamports p u c)).set 2 checkpointBytes ∧
      out.accounts=(state (triple pa ua ca) lamports p u c).accounts ∧
      out.lamports_cells=lamports ∧
      AspisR1CurrentCaller.verifier.candidate.tx1 verifierOps
        (SourceInstallation.currentDigest
          (SolanaDigest.Insts.Aspis_coreDigestDigest32 (Installation.install ops verifierOps)))
        (CurrentCarrier.toCurrentPublic (publicOf statement)) (alloc.vec.Vec.deref u.bytes)
        (FrameOperationsTotal.segment (alloc.vec.Vec.deref p.bytes) 688#usize 58295#usize)
        (splitIndex ten) () none=ok (.Ok checkpointBytes) := by
  have same := initial_identity program pa ua ca lamports p u c pMeta uMeta cMeta cFree
  have result := ReadyStatement.construct ops verifierOps program pa ua ca lamports p u c ten
    statement candidate checkpointBytes distinctPU distinctPC distinctUC proofLength checkpointLength
    outputLength proofAllowed publicAllowed scanned decoded validated encoded compared tagRead firstReturned
  simpa only [same] using result

#print axioms readonly_identity
#print axioms checkpoint_identity
#print axioms initial_identity
#print axioms construct
end AspisS2OwnedStage1.SdkReference.ReadyOriginal
