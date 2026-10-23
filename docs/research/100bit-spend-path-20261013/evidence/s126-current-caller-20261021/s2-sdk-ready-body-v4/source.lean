import S2SdkReadyCallerV1
set_option autoImplicit false
open Aeneas Aeneas.Std Result
namespace AspisS2OwnedStage1.SdkReference.ReadyBody
open ReadyState ReadyCaller
abbrev Statement := AspisS2OwnedStage1.Reachability.Statement
abbrev Common := aspis_statement.pool_v1.pair_forest_terminal.PoolV1PairForestTerminalCommonV1
abbrev Public := AspisS2OwnedStage1.Reachability.Public

private theorem zero_allowed : shared_allowed 0#isize=ok true := by
  apply (PrimitivesTotal.shared_allowed_true 0#isize).mpr
  constructor <;> scalar_tac

private theorem add_end : (688#usize+57607#usize : Result Usize)=ok 58295#usize := by
  apply AspisR1CurrentCaller.UsizeArithmetic.add_eq_ok <;> scalar_tac

private theorem checked_end : Usize.checked_add 688#usize 57607#usize=some 58295#usize := by
  unfold Usize.checked_add core.num.checked_add_UScalar
  rw [add_end]
  rfl

private theorem tag_offset : (688#usize+8#usize : Result Usize)=ok 696#usize := by
  apply AspisR1CurrentCaller.UsizeArithmetic.add_eq_ok <;> scalar_tac

/-- Forward constructor for the complete installed source reference in the
necessary accepted-native metadata class. All bytes and retained SDK fields
are the supplied initial values. No reference/body/acquire/write/release
success is a premise. Actual native observation/representation transport is
still required; the retained child observations are not silently discharged. -/
theorem construct (ops : Ops) (verifierOps : AspisR1CurrentCaller.Ops)
    (program : Array U8 32#usize) (pa ua ca : OwnedAccount)
    (lamports : alloc.vec.Vec OwnedLamportsCell) (p u c : OwnedDataCell) (ten : Bool)
    (statement : Statement) (common : Common) (pub : Public)
    (candidate : Array U8 688#usize) (checkpointBytes : alloc.vec.Vec U8)
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
    (commonRead :
      aspis_statement.pool_v1.pair_forest_terminal.PoolV1PairForestTerminalStatementV1.common statement=ok common)
    (encoded : (Installation.install ops verifierOps).op8 common.lane_transition.candidate_afterstate=
      ok (.Ok candidate))
    (compared : (Installation.install ops verifierOps).op0 core.cmp.PartialEqU8
      (FrameOperationsTotal.segment (alloc.vec.Vec.deref p.bytes) 0#usize 688#usize) candidate=ok false)
    (tagRead : alloc.vec.Vec.index (core.slice.index.SliceIndexUsizeSlice U8)
      p.bytes 696#usize=ok 2#u8)
    (projected :
      aspis_statement.pool_v1.pair_forest_terminal.PoolV1PairForestTerminalStatementV1.semantic_public statement=ok pub)
    (firstReturned : first_decoded (Installation.install ops verifierOps) pub
      (alloc.vec.Vec.deref u.bytes)
      (FrameOperationsTotal.segment (alloc.vec.Vec.deref p.bytes) 688#usize 58295#usize)
      (splitIndex ten)=ok (.Ok checkpointBytes)) :
    ∃ out, BorrowedReference.owned_stage1 (Installation.install ops verifierOps)
      program (initialSdk program pa ua ca lamports p u c) (instruction ten)=ok (.Ok (),out) := by
  let accs := accounts3 program pa ua ca
  let liveC : OwnedDataCell := {c with borrowed:=(-1)#isize}
  have cpAcquire := ReadyState.checkpoint accs lamports p u {c with borrowed:=0#isize}
    GuardAcquire.noGuards rfl
  obtain ⟨nextU,nextUValue,pubAcquire⟩ := ReadyState.public_acquire accs lamports p u liveC publicAllowed
  obtain ⟨nextP,nextPValue,proofAcquire⟩ := ReadyState.proof_acquire accs lamports p
    {u with borrowed:=nextU} liveC proofAllowed
  let finalSdk := state accs lamports {p with borrowed:=nextP} {u with borrowed:=nextU} liveC
  have cpRead : alloc.vec.Vec.index (core.slice.index.SliceIndexUsizeSlice OwnedDataCell)
      finalSdk.data_cells 2#usize=ok liveC := read_two _ _ _
  have valid : (2#usize).val<finalSdk.data_cells.val.length := by simp [finalSdk,state,triple]
  obtain ⟨actual,_,actualRead,mutableRead⟩ := BorrowTotal.cell_operations_total finalSdk 2#usize valid
  have same : actual=liveC := Result.ok.inj (actualRead.symm.trans cpRead)
  cases same
  have cpLen : alloc.vec.Vec.len c.bytes=1768#usize := by
    apply UScalar.eq_of_val_eq
    exact checkpointLength
  have pLen : alloc.vec.Vec.len p.bytes=58295#usize := by
    apply UScalar.eq_of_val_eq
    exact proofLength
  have outLen : alloc.vec.Vec.len checkpointBytes=1768#usize := by
    apply UScalar.eq_of_val_eq
    exact outputLength
  have baseCpRead : alloc.vec.Vec.index (core.slice.index.SliceIndexUsizeSlice OwnedDataCell)
      (initialSdk program pa ua ca lamports p u c).data_cells 2#usize=ok {c with borrowed:=0#isize} := read_two _ _ _
  have cpHeader : owned_data_len (initialSdk program pa ua ca lamports p u c) 2#usize=
      ok (.Ok 1768#usize) := by
    simp only [owned_data_len,baseCpRead,bind_tc_ok]
    simp [zero_allowed,cpLen]
  have accountLength : alloc.vec.Vec.len (initialSdk program pa ua ca lamports p u c).accounts=3#usize := by
    apply UScalar.eq_of_val_eq
    rfl
  have proofAccountRead : alloc.vec.Vec.index (core.slice.index.SliceIndexUsizeSlice OwnedAccount)
      (initialSdk program pa ua ca lamports p u c).accounts 0#usize=ok (readonlyMeta pa 0#usize) := read_zero _ _ _
  have publicAccountRead : alloc.vec.Vec.index (core.slice.index.SliceIndexUsizeSlice OwnedAccount)
      (initialSdk program pa ua ca lamports p u c).accounts 1#usize=ok (readonlyMeta ua 1#usize) := read_one _ _ _
  have checkpointAccountRead : alloc.vec.Vec.index (core.slice.index.SliceIndexUsizeSlice OwnedAccount)
      (initialSdk program pa ua ca lamports p u c).accounts 2#usize=ok (checkpointMeta program ca) := read_two _ _ _
  have cpAcquireN : owned_acquire_checkpoint (initialSdk program pa ua ca lamports p u c)
      GuardAcquire.noGuards 2#usize=ok (.Ok (),state accs lamports p u liveC,
        {GuardAcquire.noGuards with checkpoint:=some 2#usize}) := cpAcquire
  have liveCpRead : alloc.vec.Vec.index (core.slice.index.SliceIndexUsizeSlice OwnedDataCell)
      (state accs lamports p u liveC).data_cells 2#usize=ok liveC := read_two _ _ _
  have publicCellRead : alloc.vec.Vec.index (core.slice.index.SliceIndexUsizeSlice OwnedDataCell)
      (state accs lamports p {u with borrowed:=nextU} liveC).data_cells 1#usize=
        ok {u with borrowed:=nextU} := read_one _ _ _
  have proofCellRead : alloc.vec.Vec.index (core.slice.index.SliceIndexUsizeSlice OwnedDataCell)
      finalSdk.data_cells 0#usize=ok {p with borrowed:=nextP} := read_zero _ _ _
  have pref := FrameOperationsTotal.prefix_range_total p.bytes 688#usize (by simp only [proofLength];decide)
  have suff := FrameOperationsTotal.range_total p.bytes 688#usize 58295#usize
    (by decide) (by simp only [proofLength];decide)
  have i10 : (Installation.install ops verifierOps).op1 core.cmp.PartialEqU8
      (alloc.vec.Vec.deref (instruction ten)) (Array.make 2#usize [3#u8,10#u8])=ok ten := instruction_ten ten
  have i11 : (Installation.install ops verifierOps).op1 core.cmp.PartialEqU8
      (alloc.vec.Vec.deref (instruction ten)) (Array.make 2#usize [3#u8,11#u8])=ok (!ten) := instruction_eleven ten
  have constants4 : (Installation.install ops verifierOps).op4=ok 57607#usize := rfl
  have constants7 : (Installation.install ops verifierOps).op7=ok 688#usize := rfl
  have optionEnd : (Installation.install ops verifierOps).op2 (some 58295#usize)
      solana_program_error.ProgramError.InvalidAccountData=ok (.Ok 58295#usize) := rfl
  have liveCBytes : liveC.bytes=c.bytes := rfl
  dsimp only [finalSdk] at proofCellRead cpRead mutableRead
  simp only [alloc.vec.Vec.index_slice_index] at liveCpRead publicCellRead proofCellRead cpRead
  simp only [alloc.vec.Vec.index_mut_slice_index] at mutableRead
  simp only [alloc.vec.Vec.index_slice_index] at tagRead
  have castValue : UScalar.cast .Usize (splitByte ten)=splitIndex ten := by
    have castRun := instruction_cast ten
    change ok (UScalar.cast .Usize (splitByte ten))=ok (splitIndex ten) at castRun
    exact Result.ok.inj castRun
  have body : ∃ bodyOut guards, owned_stage1_body (Installation.install ops verifierOps)
      program (initialSdk program pa ua ca lamports p u c)
      (alloc.vec.Vec.deref (instruction ten)) GuardAcquire.noGuards=ok (.Ok (),bodyOut,guards) := by
    cases ten <;>
      simp [owned_stage1_body,i10,i11,accountLength,proofAccountRead,publicAccountRead,
        checkpointAccountRead,readonlyMeta,checkpointMeta,
        key_eq_false _ _ distinctPU,key_eq_false _ _ distinctPC,
        key_eq_false _ _ distinctUC,owner_ne_self,cpHeader,CheckpointSizeTotal.checkpoint_size_S2,
        cpAcquireN,liveCpRead,pubAcquire,publicCellRead,proofAcquire,proofCellRead,
        PrimitivesTotal.bytes_clone_total,scanned,decoded,validated,commonRead,encoded,
        constants4,constants7,checked_end,optionEnd,pLen,pref,compared,tag_offset,tagRead,
        aspis_r1_cost_probe.transport.Variant.tag,projected,suff,instruction_read,instruction_cast,
        firstReturned,outLen,cpLen,cpRead,mutableRead,liveCBytes,castValue,
        proofLength,checkpointLength,outputLength,
        core.result.Result.Insts.CoreOpsTry.branch,core.result.Result.map_err,lift,Aeneas.Std.uncurry] <;>
      exact ⟨_,_,rfl⟩
  obtain ⟨bodyOut,guards,bodyRun⟩ := body
  obtain ⟨out,run⟩ := GuardBody.body_return_finalizes (Installation.install ops verifierOps)
    program (initialSdk program pa ua ca lamports p u c) bodyOut (instruction ten) (.Ok ()) guards bodyRun
  exact ⟨out,by rw [BorrowedEquivalence.stage1_eq];exact run⟩

#print axioms construct
end AspisS2OwnedStage1.SdkReference.ReadyBody
