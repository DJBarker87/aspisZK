import S2A_InstalledCuts

/-! Same original records and child carriers as ReadyRawInputs.construct.
Only its redundant validator hypothesis is discharged here; native admission
and all actual execution/cut binding obligations are unchanged. -/
set_option autoImplicit false
open Aeneas Aeneas.Std Result
namespace AspisR1.S2A
open AspisS2OwnedStage1 AspisS2OwnedStage1.SdkReference
open ReadyState ReadyCaller ReadyStatement
theorem construct_without_validator (ops : SdkReference.Ops) (verifierOps : AspisR1CurrentCaller.Ops)
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
  obtain ⟨decodedStatement, decoderReturned, sameStatement, publicLength, validated⟩ :=
    InstalledCuts.decoded ops verifierOps (alloc.vec.Vec.deref u.bytes) statement decoded
  exact ReadyRawInputs.construct ops verifierOps program pa ua ca lamports p u c ten
    statement candidate checkpointBytes pMeta uMeta cMeta cFree distinctPU distinctPC distinctUC
    proofLength checkpointLength outputLength proofCounter publicCounter checkpointZero
    decoded validated encoded prefixBytes tagByte firstReturned

#print axioms construct_without_validator
end AspisR1.S2A
