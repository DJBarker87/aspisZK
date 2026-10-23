import S2OwnedCurrentCarrierV1
import S2OwnedSnapshotTransportV1
import CurrentCallerUsizeArithmeticV1
set_option autoImplicit false
open Aeneas Aeneas.Std Result
namespace AspisS2OwnedStage1.SourceInstallation
open AspisS2OwnedStage1 CurrentCarrier

def currentDigest {H : Type} (d : aspis_core.digest.Digest32 H) :
    AspisR1CurrentCaller.aspis_core.digest.Digest32 H :=
  {coremarkerCopyInst:=d.coremarkerCopyInst,digest:=d.digest}

def currentPhase : AspisR1CurrentCaller.verifier.Phase → aspis_r1_cost_probe.verifier.Phase
  | .Parsed => .Parsed
  | .Semantic => .Semantic
  | .SemanticPart i => .SemanticPart i
  | .Prepare => .Prepare
  | .CheckpointRead => .CheckpointRead
  | .Merkle i => .Merkle i
  | .Query i => .Query i
  | .QueryPart i j => .QueryPart i j
  | .CheckpointWrite => .CheckpointWrite
  | .Relation => .Relation
  | .Final => .Final

def freshError : AspisR1CurrentCaller.verifier.Error → aspis_r1_cost_probe.verifier.Error
  | .Parse => .Parse
  | .Semantic => .Semantic
  | .Transcript => .Transcript
  | .Relation => .Relation
  | .Merkle => .Merkle
  | .Query => .Query
  | .Checkpoint => .Checkpoint
  | .Allocation => .Allocation

def currentError : aspis_r1_cost_probe.verifier.Error → AspisR1CurrentCaller.verifier.Error
  | .Parse => .Parse
  | .Semantic => .Semantic
  | .Transcript => .Transcript
  | .Relation => .Relation
  | .Merkle => .Merkle
  | .Query => .Query
  | .Checkpoint => .Checkpoint
  | .Allocation => .Allocation

theorem error_roundtrip (e : AspisR1CurrentCaller.verifier.Error) :
    currentError (freshError e)=e := by cases e <;> rfl

def actualDecoder (bytes : Slice U8) :
    Result (core.result.Result Reachability.Statement
      aspis_statement.pool_v1.pair_forest_terminal.PoolV1PairForestTerminalFormatErrorV1) := do
  let r ← AspisR1PublicPreparation.S6DecoderScopedReuseV1.decodeActual bytes
  match r with
  | .Ok s => ok (.Ok (fromDecoderStatement s))
  | .Err e => ok (.Err (fromDecoderDecodeError e))

def currentChild (verifierOps : AspisR1CurrentCaller.Ops) {H : Type}
    (d : aspis_core.digest.Digest32 H) (pub : Reachability.Public)
    (bytes proof : Slice U8) (k : Usize) (hash : H)
    (observer : Option (aspis_r1_cost_probe.verifier.Phase → Result Unit)) :
    Result (core.result.Result (alloc.vec.Vec U8) aspis_r1_cost_probe.verifier.Error) := do
  let r ← AspisR1CurrentCaller.verifier.candidate.tx1 verifierOps (currentDigest d)
    (toCurrentPublic pub) bytes proof k hash
    (observer.map fun callback => fun phase => callback (currentPhase phase))
  match r with
  | .Ok cp => ok (.Ok cp)
  | .Err e => ok (.Err (freshError e))

/-- Exact Option.ok_or body of the retained RustStd emission; no callback. -/
def stdOption {T E : Type} (o : Option T) (e : E) : Result (core.result.Result T E) :=
  match o with
  | none => ok (.Err e)
  | some value => ok (.Ok value)

/-- Actual U8 slice/array comparator is supplied through the library's
slice comparator with the array's exact slice. No free guard callback. -/
def stdSliceArrayNe {T U : Type} {N : Usize} (cmp : core.cmp.PartialEq T U)
    (bytes : Slice T) (array : Array U N) : Result Bool :=
  core.slice.cmp.PartialEqSlice.ne cmp bytes (Array.to_slice array)

def install (ops : Ops) (verifierOps : AspisR1CurrentCaller.Ops) : Ops :=
  {ops with
    op0:=@stdSliceArrayNe,
    op1:=@stdOption,
    op2:=@currentChild verifierOps,
    op3:=ok 57607#usize,
    op5:=actualDecoder,
    op6:=ok 688#usize,
    op8:=fun _ => ok ()}

theorem checked_end_total :
    Usize.checked_add 688#usize 57607#usize=some 58295#usize := by
  have h : (688#usize+57607#usize : Result Usize)=ok 58295#usize := by
    apply AspisR1CurrentCaller.UsizeArithmetic.add_eq_ok <;> scalar_tac
  unfold Usize.checked_add core.num.checked_add_UScalar
  rw [h]
  rfl

theorem tag_offset_total : (688#usize+8#usize : Result Usize)=ok 696#usize := by
  apply AspisR1CurrentCaller.UsizeArithmetic.add_eq_ok <;> scalar_tac

private theorem bind_success {A B : Type} (m : Result A) (f : A → Result B) (out : B)
    (h : (do let a ← m; f a)=ok out) : ∃ a,m=ok a ∧ f a=ok out := by
  cases m with
  | ok a => exact ⟨a,rfl,h⟩
  | fail e => simp only [bind_tc_fail] at h; cases h
  | div => simp only [bind_tc_div] at h; cases h

theorem decoder_success (bytes : Slice U8) (statement : Reachability.Statement)
    (h : actualDecoder bytes=ok (.Ok statement)) :
    ∃ s : AspisR1TerminalDecoder.PublicBinding.Statement,
      AspisR1PublicPreparation.S6DecoderScopedReuseV1.decodeActual bytes=ok (.Ok s) ∧
      statement=fromDecoderStatement s := by
  unfold actualDecoder at h
  obtain ⟨r,hr,h⟩ := bind_success _ _ _ h
  cases r with
  | Err e => cases h
  | Ok s => cases h; exact ⟨s,hr,rfl⟩

theorem boxed_success (ops : Ops) (bytes : Slice U8) (statement : Reachability.Statement)
    (h : decode_public_statement_box ops bytes=ok (.Ok statement)) :
    ops.op5 bytes=ok (.Ok statement) := by
  unfold decode_public_statement_box at h
  obtain ⟨r,hr,h⟩ := bind_success _ _ _ h
  cases r with
  | Err e =>
    simp only [core.result.Result.map_err,
      decode_public_statement_box.closure.Insts.CoreOpsFunctionFnOnceTuplePoolV1PairForestTerminalFormatErrorV1ProgramError,
      decode_public_statement_box.closure.Insts.CoreOpsFunctionFnOnceTuplePoolV1PairForestTerminalFormatErrorV1ProgramError.call_once,
      core.result.Result.Insts.CoreOpsTry.branch,
      core.result.Result.Insts.CoreOpsTryTraitFromResidualResultInfallible.from_residual,
      core.convert.FromSame.from,bind_tc_ok] at h
    cases h
  | Ok s =>
    simp only [core.result.Result.map_err,core.result.Result.Insts.CoreOpsTry.branch,bind_tc_ok] at h
    cases h
    exact hr

theorem child_success (verifierOps : AspisR1CurrentCaller.Ops)
    {H : Type} (d : aspis_core.digest.Digest32 H) (pub : Reachability.Public)
    (bytes proof : Slice U8) (k : Usize) (hash : H) (cp : alloc.vec.Vec U8)
    (h : currentChild verifierOps d pub bytes proof k hash none=ok (.Ok cp)) :
    AspisR1CurrentCaller.verifier.candidate.tx1 verifierOps (currentDigest d)
      (toCurrentPublic pub) bytes proof k hash none=ok (.Ok cp) := by
  unfold currentChild at h
  obtain ⟨r,hr,h⟩ := bind_success _ _ _ h
  cases r with
  | Err e => cases h
  | Ok value => cases h; exact hr

/-- The enclosing emitted reference now runs the actual retained decoder and
current compact tx1 on field/constructor-preserving carriers. From one success,
derive the same actual decoder instance, same-byte firstCurrent execution,
exact proof frame and checkpoint write. No decoder or selected-child premise.
The ordered SDK-read, validation, encoding, hash and error/log interpretations
remain explicit fields, not assertions that the SDK instance is already closed. -/
theorem tail_current_first (ops : Ops) (verifierOps : AspisR1CurrentCaller.Ops)
    (checkpointIn data checkpointOut : Slice U8)
    (h : owned_stage1_tail (install ops verifierOps) checkpointIn data=ok (.Ok (),checkpointOut)) :
    ∃ (publicData proofData : alloc.vec.Vec U8)
      (statement : AspisR1TerminalDecoder.PublicBinding.Statement)
      (selected : Slice U8) (splitByte : U8) (k : Usize) (cp : alloc.vec.Vec U8),
      ops.op11=ok (.Ok publicData) ∧ ops.op12=ok (.Ok proofData) ∧
      AspisR1PublicPreparation.S6DecoderScopedReuseV1.decodeActual
        (alloc.vec.Vec.deref publicData)=ok (.Ok statement) ∧
      alloc.vec.Vec.index (core.slice.index.SliceIndexRangeUsizeSlice U8) proofData
        {start:=688#usize,«end»:=58295#usize}=ok selected ∧
      Slice.index_usize data 1#usize=ok splitByte ∧
      lift (UScalar.cast .Usize splitByte)=ok k ∧
      AspisR1CurrentCaller.FirstComposition.firstCurrent
        solana_program_error.ProgramError.InvalidAccountData verifierOps
        (currentDigest (SolanaDigest.Insts.Aspis_coreDigestDigest32 (install ops verifierOps)))
        (fun e => ops.op10 (freshError e)) (alloc.vec.Vec.deref publicData) selected k=ok (.Ok cp) ∧
      core.slice.Slice.copy_from_slice core.marker.CopyU8 checkpointIn
        (alloc.vec.Vec.deref cp)=ok checkpointOut := by
  obtain ⟨publicData,proofData,statement,pub,selected,proofLength,proofStart,proofEnd,
    checkedEnd,splitByte,k,cp,hpublic,hbox,hproof,hlength,hstart,hchecked,hend,hselected,
    hbyte,hcast,hpub,hfirst,hchild,hcopy⟩ :=
    Reachability.tail_success (install ops verifierOps) checkpointIn data checkpointOut h
  have hl : proofLength=57607#usize := (Result.ok.inj hlength).symm
  have hs : proofStart=688#usize := (Result.ok.inj hstart).symm
  subst proofLength; subst proofStart
  have he : checkedEnd=some 58295#usize := by
    rw [checked_end_total] at hchecked
    exact (Result.ok.inj hchecked).symm
  subst checkedEnd
  have he : proofEnd=58295#usize := by
    change ok (core.result.Result.Ok 58295#usize)=ok (.Ok proofEnd) at hend
    exact (core.result.Result.Ok.inj (Result.ok.inj hend)).symm
  subst proofEnd
  obtain ⟨decoded,hdecode,hstatement⟩ := decoder_success _ statement
    (boxed_success (install ops verifierOps) _ statement hbox)
  subst statement
  have hpublicSelection : toCurrentPublic pub =
      AspisR1CurrentCaller.FirstComposition.toCurrentPublic
        (AspisR1PublicPreparation.PreparationBinding.preparationPublic decoded) := by
    have hp := selected_public decoded
    rw [hpub] at hp
    exact Result.ok.inj hp
  have htx := child_success verifierOps
    (SolanaDigest.Insts.Aspis_coreDigestDigest32 (install ops verifierOps)) pub
    (alloc.vec.Vec.deref publicData) selected k () cp hchild
  rw [hpublicSelection] at htx
  refine ⟨publicData,proofData,decoded,selected,splitByte,k,cp,hpublic,hproof,hdecode,
    hselected,hbyte,hcast,?_,hcopy⟩
  unfold AspisR1CurrentCaller.FirstComposition.firstCurrent
  rw [AspisR1PublicPreparation.RepinS6First.reuse_decoded _ _ _ _ _ _ _ hdecode]
  unfold AspisR1PublicPreparation.RepinS6First.first_decoded
    AspisR1PublicPreparation.RepinS6First.observer
    AspisR1CurrentCaller.FirstComposition.currentTx1
  simp only [bind_tc_ok,Option.map_none,htx,
    AspisR1PublicPreparation.core.result.Result.map_err]

#print axioms error_roundtrip
#print axioms checked_end_total
#print axioms tag_offset_total
#print axioms decoder_success
#print axioms boxed_success
#print axioms child_success
#print axioms tail_current_first
end AspisS2OwnedStage1.SourceInstallation
