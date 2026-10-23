import S2F_Stage2Cuts
set_option autoImplicit false
open Aeneas Aeneas.Std Result AspisS2OwnedStage1
namespace AspisR1.S2F
open S2E_Reference.S2E_Reference AspisR1.S2E

/-- Derived reference cuts only. The original state/input indices are fixed and
all intermediate states come from the extracted computation. No native run or
concrete Children/Ops interpretation is hidden in this carrier. -/
structure Stage2Certificate {C S : Type} (ops : S2E_Reference.Ops)
    (children : Children C S) (original : Original S) (finalState : S) (finalSdk : SDK) where
  cleared : S
  validatedState : S
  validated : Validated
  beforeStatementDrop : S
  proofAccount : OwnedAccount
  checkpointAccount : OwnedAccount
  acquiredProof : SDK
  acquiredCheckpoint : SDK
  beforeProofDrop : SDK
  proofCell : OwnedDataCell
  checkpointCell : OwnedDataCell
  checkedEnd : Option Usize
  endOffset : Usize
  publicBytes : alloc.vec.Vec U8
  encodedState : S
  expectedLength : Usize
  selected : Slice U8
  secondState : S
  clear : children.clear_return_data original.state = ok cleared
  validate : children.validate_asq8 cleared original.program original.sdk original.data = ok (.Ok validated,validatedState)
  proofRead : alloc.vec.Vec.index (core.slice.index.SliceIndexUsizeSlice OwnedAccount) original.sdk.accounts 0#usize = ok proofAccount
  proofBorrow : owned_acquire_shared original.sdk proofAccount.data_slot = ok (.Ok (),acquiredProof)
  checkpointRead : alloc.vec.Vec.index (core.slice.index.SliceIndexUsizeSlice OwnedAccount) acquiredProof.accounts 6#usize = ok checkpointAccount
  checkpointBorrow : owned_acquire_shared acquiredProof checkpointAccount.data_slot = ok (.Ok (),acquiredCheckpoint)
  proofCellRead : alloc.vec.Vec.index (core.slice.index.SliceIndexUsizeSlice OwnedDataCell) acquiredCheckpoint.data_cells proofAccount.data_slot = ok proofCell
  checked : lift (Usize.checked_add 688#usize validated.proof_length) = ok checkedEnd
  endResult : ops.op2 checkedEnd solana_program_error.ProgramError.InvalidAccountData = ok (.Ok endOffset)
  proofLength : alloc.vec.Vec.len proofCell.bytes = endOffset
  publicEncoded : children.«public» validatedState validated.statement = ok (.Ok publicBytes,encodedState)
  expected : ops.op12 = ok expectedLength
  publicLength : alloc.vec.Vec.len publicBytes = expectedLength
  range : alloc.vec.Vec.index (core.slice.index.SliceIndexRangeUsizeSlice U8) proofCell.bytes {start:=688#usize,«end»:=endOffset} = ok selected
  checkpointCellRead : alloc.vec.Vec.index (core.slice.index.SliceIndexUsizeSlice OwnedDataCell) acquiredCheckpoint.data_cells checkpointAccount.data_slot = ok checkpointCell
  second : children.second encodedState publicBytes.deref selected checkpointCell.bytes.deref = ok (.Ok (),secondState)
  emit : children.emit secondState validated.statement = ok (.Ok (),beforeStatementDrop)
  checkpointDrop : release_shared acquiredCheckpoint checkpointAccount.data_slot = ok beforeProofDrop
  proofDrop : release_shared beforeProofDrop proofAccount.data_slot = ok finalSdk
  statementDrop : children.drop_statement beforeStatementDrop validated.statement = ok finalState

/-- Closes the previously missing stage2 REFERENCE composition. Its sole success
input is extracted stage2 success, not independently selected child observations. -/
theorem stage2_certificate {C S : Type} (ops : S2E_Reference.Ops)
    (children : Children C S) (original : Original S) (finalState : S) (finalSdk : SDK)
    (accepted : stage2 ops children original.state original.sdk original.program original.data =
      ok (.Ok (),finalState,finalSdk)) :
    Nonempty (Stage2Certificate ops children original finalState finalSdk) := by
  obtain ⟨cleared,sv,validated,sb,hclear,hvalidate,hproof,hstatementDrop⟩ :=
    stage2_prefix ops children original finalState finalSdk accepted
  obtain ⟨pa,hp,hpd,hpa,hpb,hcp,hproofDrop⟩ :=
    stage2_proof_cut ops children sv sb original.sdk finalSdk validated hproof
  obtain ⟨ca,hc,hca,hcb,htail,hcpDrop⟩ :=
    stage2_checkpoint_cut ops children sv sb hp hpd validated pa.data_slot hcp
  obtain ⟨pc,checkedEnd,endOffset,publicBytes,se,expectedLength,selected,cc,ss,
    hchecked,hend,hpc,hlen,hpublic,hexpected,hpublicLength,hrange,hcc,hsecond,hemit⟩ :=
    stage2_tail_cut ops children sv sb hc validated pa.data_slot ca.data_slot htail
  exact ⟨{
    cleared:=cleared,validatedState:=sv,validated:=validated,beforeStatementDrop:=sb,
    proofAccount:=pa,checkpointAccount:=ca,acquiredProof:=hp,acquiredCheckpoint:=hc,
    beforeProofDrop:=hpd,proofCell:=pc,checkpointCell:=cc,checkedEnd:=checkedEnd,
    endOffset:=endOffset,publicBytes:=publicBytes,encodedState:=se,expectedLength:=expectedLength,
    selected:=selected,secondState:=ss,clear:=hclear,validate:=hvalidate,
    proofRead:=hpa,proofBorrow:=hpb,checkpointRead:=hca,checkpointBorrow:=hcb,
    proofCellRead:=hpc,checked:=hchecked,endResult:=hend,proofLength:=hlen,
    publicEncoded:=hpublic,expected:=hexpected,publicLength:=hpublicLength,
    range:=hrange,checkpointCellRead:=hcc,second:=hsecond,emit:=hemit,
    checkpointDrop:=hcpDrop,proofDrop:=hproofDrop,statementDrop:=hstatementDrop }⟩

#print axioms stage2_certificate
end AspisR1.S2F
