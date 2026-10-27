import RPz7_S2SdkReadyOriginalV1
import S2CheckpointGuardTransportV1
set_option autoImplicit false
open Aeneas Aeneas.Std Result
namespace AspisS2OwnedStage1.SdkReference.ReadyRawInputs
open ReadyState ReadyCaller ReadyStatement

theorem scan_zero (bytes : alloc.vec.Vec U8) (zero : ∀ byte ∈ bytes.val,byte=0#u8) :
    owned_checkpoint_nonzero bytes=ok false := by
  rw [ScanTotal.scan_eq,CheckpointGuardTransport.owned_eq_std,
    (CheckpointGuardTransport.stdAny_false bytes.val).mpr zero]

theorem prefix_equal (ops : Ops) (verifierOps : AspisR1CurrentCaller.Ops)
    (bytes : alloc.vec.Vec U8) (candidate : Array U8 688#usize)
    (same : bytes.val.take 688=candidate.val) :
    (Installation.install ops verifierOps).op0 core.cmp.PartialEqU8
      (FrameOperationsTotal.segment (alloc.vec.Vec.deref bytes) 0#usize 688#usize) candidate=ok false := by
  change core.slice.cmp.PartialEqSlice.ne core.cmp.PartialEqU8
    (FrameOperationsTotal.segment (alloc.vec.Vec.deref bytes) 0#usize 688#usize)
    (Array.to_slice candidate)=ok false
  rw [ProofGate.standard_ne]
  simp [FrameOperationsTotal.segment,FrameOperationsTotal.deref_val,Array.to_slice,same]

theorem tag_value (bytes : alloc.vec.Vec U8) (tag : bytes.val[696]?=some 2#u8) :
    alloc.vec.Vec.index (core.slice.index.SliceIndexUsizeSlice U8) bytes 696#usize=ok 2#u8 := by
  simp [alloc.vec.Vec.index_slice_index,alloc.vec.Vec.index_usize,tag]

/-- COMPLETE original-state installed caller from byte/scalar guard facts.
No caller, SDK acquisition, scan/comparison/index operation, write, release or
independent projection success is a premise. Only the actual decode, validator,
encoder and first return observations remain, plus raw admission facts. This
is not a native SDK/SBF or cross-transaction correspondence assertion. -/
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
    (proofCounter : p.borrowed≥0#isize ∧ p.borrowed<core.num.Isize.MAX)
    (publicCounter : u.borrowed≥0#isize ∧ u.borrowed<core.num.Isize.MAX)
    (checkpointZero : ∀ byte ∈ c.bytes.val,byte=0#u8)
    (decoded : decode_public_statement_box (Installation.install ops verifierOps)
      (alloc.vec.Vec.deref u.bytes)=ok (.Ok statement))
    (validated : (Installation.install ops verifierOps).op5 statement=ok (.Ok ()))
    (encoded : (Installation.install ops verifierOps).op8 (commonOf statement).lane_transition.candidate_afterstate=
      ok (.Ok candidate))
    (prefixBytes : p.bytes.val.take 688=candidate.val)
    (tagByte : p.bytes.val[696]?=some 2#u8)
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
  have proofAllowed := (PrimitivesTotal.shared_allowed_true p.borrowed).mpr proofCounter
  have publicAllowed := (PrimitivesTotal.shared_allowed_true u.borrowed).mpr publicCounter
  exact ReadyOriginal.construct ops verifierOps program pa ua ca lamports p u c ten
    statement candidate checkpointBytes pMeta uMeta cMeta cFree distinctPU distinctPC distinctUC
    proofLength checkpointLength outputLength proofAllowed publicAllowed (scan_zero c.bytes checkpointZero)
    decoded validated encoded (prefix_equal ops verifierOps p.bytes candidate prefixBytes)
    (tag_value p.bytes tagByte) firstReturned

#print axioms scan_zero
#print axioms prefix_equal
#print axioms tag_value
#print axioms construct
end AspisS2OwnedStage1.SdkReference.ReadyRawInputs
