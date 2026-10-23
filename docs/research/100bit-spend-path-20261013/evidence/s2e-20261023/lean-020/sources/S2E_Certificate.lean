import S2E_Execution
set_option autoImplicit false
open Aeneas Aeneas.Std Result AspisS2OwnedStage1
namespace AspisR1.S2E
open S2E_Reference.S2E_Reference

/-- A reference trace, rooted at fixed original inputs. Child states and SDK
states are threaded through every reached continuation. This record is a
conclusion of reference success inversion, never a replacement native premise. -/
structure ReferenceCertificate {C S : Type} (ops : S2E_Reference.Ops)
    (children : Children C S) (original : Original S) (finalState : S) (finalSdk : SDK) where
  cpAccount cpScanAccount pubAccount proofAccount cpAtProof : OwnedAccount
  cpCell pubCell proofCell copyCell : OwnedDataCell
  acquiredCP acquiredPublic acquiredProof : SDK
  beforeCpDrop beforePublicDrop beforeProofDrop : SDK
  guards : LiveGuards
  publicBytes proofBytes checkpoint : alloc.vec.Vec U8
  selected : Slice U8
  statement : Statement
  candidate : Array U8 688#usize
  splitByte : U8
  split : Usize
  afterDecode afterValidate afterEncode afterFirst afterCopy beforeStatementDrop : S
  shape : shape1 ops original.data (alloc.vec.Vec.len original.sdk.accounts) = ok (.Ok ())
  admitted : admission ops original.program original.sdk = ok (.Ok ())
  cpRead : alloc.vec.Vec.index (core.slice.index.SliceIndexUsizeSlice OwnedAccount)
    original.sdk.accounts 2#usize = ok cpAccount
  cpBorrow : owned_acquire_checkpoint original.sdk
    {checkpoint:=none,«public»:=none,proof:=none} cpAccount.data_slot = ok (.Ok (),acquiredCP,guards)
  cpBody : checkpoint_continuation ops children original.state acquiredCP original.data =
    ok (.Ok (),finalState,beforeCpDrop)
  cpScanRead : alloc.vec.Vec.index (core.slice.index.SliceIndexUsizeSlice OwnedAccount)
    acquiredCP.accounts 2#usize = ok cpScanAccount
  cpCellRead : alloc.vec.Vec.index (core.slice.index.SliceIndexUsizeSlice OwnedDataCell)
    acquiredCP.data_cells cpScanAccount.data_slot = ok cpCell
  scan : nonzero_from cpCell.bytes.deref (alloc.vec.Vec.len cpCell.bytes) = ok false
  publicBody : public_continuation ops children original.state acquiredCP original.data =
    ok (.Ok (),finalState,beforeCpDrop)
  publicRead : alloc.vec.Vec.index (core.slice.index.SliceIndexUsizeSlice OwnedAccount)
    acquiredCP.accounts 1#usize = ok pubAccount
  publicBorrow : owned_acquire_shared acquiredCP pubAccount.data_slot = ok (.Ok (),acquiredPublic)
  publicCellRead : alloc.vec.Vec.index (core.slice.index.SliceIndexUsizeSlice OwnedDataCell)
    acquiredPublic.data_cells pubAccount.data_slot = ok pubCell
  publicClone : alloc.vec.CloneVec.clone core.clone.CloneU8 pubCell.bytes = ok publicBytes
  decodedBody : decoded_continuation ops children original.state acquiredPublic publicBytes.deref original.data =
    ok (.Ok (),finalState,beforePublicDrop)
  decoded : children.decode original.state publicBytes.deref = ok (.Ok statement,afterDecode)
  statementBody : statement_continuation ops children afterDecode acquiredPublic statement publicBytes.deref original.data =
    ok (.Ok (),beforeStatementDrop,beforePublicDrop)
  validated : children.validate afterDecode statement = ok (.Ok (),afterValidate)
  encoded : children.candidate afterValidate (commonOf statement).lane_transition.candidate_afterstate =
    ok (.Ok candidate,afterEncode)
  proofBody : proof_continuation ops children afterEncode acquiredPublic statement publicBytes.deref original.data candidate =
    ok (.Ok (),beforeStatementDrop,beforePublicDrop)
  proofRead : alloc.vec.Vec.index (core.slice.index.SliceIndexUsizeSlice OwnedAccount)
    acquiredPublic.accounts 0#usize = ok proofAccount
  cpReadAtProof : alloc.vec.Vec.index (core.slice.index.SliceIndexUsizeSlice OwnedAccount)
    acquiredPublic.accounts 2#usize = ok cpAtProof
  proofBorrow : owned_acquire_shared acquiredPublic proofAccount.data_slot = ok (.Ok (),acquiredProof)
  proofCellRead : alloc.vec.Vec.index (core.slice.index.SliceIndexUsizeSlice OwnedDataCell)
    acquiredProof.data_cells proofAccount.data_slot = ok proofCell
  proofClone : alloc.vec.CloneVec.clone core.clone.CloneU8 proofCell.bytes = ok proofBytes
  gate : proof_gate ops proofBytes.deref candidate = ok (.Ok ())
  splitRead : Slice.index_usize original.data 1#usize = ok splitByte
  splitCast : lift (UScalar.cast .Usize splitByte) = ok split
  firstBody : first_and_copy children afterEncode acquiredProof statement publicBytes.deref proofBytes.deref split cpAtProof.data_slot =
    ok (.Ok (),beforeStatementDrop,beforeProofDrop)
  range : core.slice.index.Slice.index (core.slice.index.SliceIndexRangeUsizeSlice U8)
    proofBytes.deref {start:=688#usize,«end»:=58295#usize} = ok selected
  firstReturned : children.first afterEncode statement publicBytes.deref selected split =
    ok (.Ok checkpoint,afterFirst)
  copyBody : after_first children afterFirst acquiredProof cpAtProof.data_slot checkpoint =
    ok (.Ok (),beforeStatementDrop,beforeProofDrop)
  copyCellRead : alloc.vec.Vec.index (core.slice.index.SliceIndexUsizeSlice OwnedDataCell)
    acquiredProof.data_cells cpAtProof.data_slot = ok copyCell
  length : alloc.vec.Vec.len checkpoint = alloc.vec.Vec.len copyCell.bytes
  copied : children.copy afterFirst acquiredProof cpAtProof.data_slot checkpoint.deref = ok (afterCopy,beforeProofDrop)
  checkpointDrop : children.drop_checkpoint afterCopy checkpoint = ok beforeStatementDrop
  proofDrop : release_shared beforeProofDrop proofAccount.data_slot = ok beforePublicDrop
  statementDrop : children.drop_statement beforeStatementDrop statement = ok finalState
  publicDrop : release_shared beforePublicDrop pubAccount.data_slot = ok beforeCpDrop
  cpDrop : owned_release_guards beforeCpDrop guards = ok finalSdk

/-- All successful child observations and cleanup cuts are DERIVED from the
same extracted E. Native success, original-byte transport, installed contracts,
SDK token interpretation and event reification are not consequences of this law. -/
theorem reference_certificate {C S : Type} (ops : S2E_Reference.Ops)
    (children : Children C S) (original : Original S) (finalState : S) (finalSdk : SDK)
    (accepted : E ops children original = ok (.Ok (),finalState,finalSdk)) :
    Nonempty (ReferenceCertificate ops children original finalState finalSdk) := by
  obtain ⟨ca,hc,guards,h0,shape,admitted,cpRead,cpBorrow,cpBody,cpDrop⟩ :=
    execution_prefix ops children original finalState finalSdk accepted
  obtain ⟨ca',cc,cpRead',cpCellRead,scan,publicBody⟩ :=
    checkpoint_success ops children original.state finalState hc h0 original.data cpBody
  obtain ⟨ua,hu,uc,pubBytes,hd,publicRead,publicBorrow,publicCellRead,publicClone,decodedBody,publicDrop⟩ :=
    public_success ops children original.state finalState hc h0 original.data publicBody
  obtain ⟨stmt,sd,sb,decoded,statementBody,statementDrop⟩ :=
    decoded_success ops children original.state finalState hu hd pubBytes.deref original.data decodedBody
  obtain ⟨sv,se,candidate,validated,encoded,proofBody⟩ :=
    statement_success ops children sd sb hu hd stmt pubBytes.deref original.data statementBody
  obtain ⟨pa,ca2,hp,pc,proofBytes,splitByte,split,hf,proofRead,cpReadAtProof,proofBorrow,
    proofCellRead,proofClone,gate,splitRead,splitCast,firstBody,proofDrop⟩ :=
    proof_success ops children se sb hu hd stmt pubBytes.deref original.data candidate proofBody
  obtain ⟨selected,checkpoint,sf,range,firstReturned,copyBody⟩ :=
    first_success children se sb hp hf stmt pubBytes.deref proofBytes.deref split ca2.data_slot firstBody
  obtain ⟨copyCell,sc,copyCellRead,length,copied,checkpointDrop⟩ :=
    after_first_success children sf sb hp hf ca2.data_slot checkpoint copyBody
  exact ⟨{
    cpAccount:=ca, cpScanAccount:=ca', pubAccount:=ua, proofAccount:=pa, cpAtProof:=ca2,
    cpCell:=cc, pubCell:=uc, proofCell:=pc, copyCell:=copyCell,
    acquiredCP:=hc, acquiredPublic:=hu, acquiredProof:=hp,
    beforeCpDrop:=h0, beforePublicDrop:=hd, beforeProofDrop:=hf,
    guards:=guards, publicBytes:=pubBytes, proofBytes:=proofBytes, checkpoint:=checkpoint,
    selected:=selected, statement:=stmt, candidate:=candidate, splitByte:=splitByte, split:=split,
    afterDecode:=sd, afterValidate:=sv, afterEncode:=se, afterFirst:=sf, afterCopy:=sc,
    beforeStatementDrop:=sb, shape:=shape, admitted:=admitted, cpRead:=cpRead,cpBorrow:=cpBorrow,
    cpBody:=cpBody,cpScanRead:=cpRead',cpCellRead:=cpCellRead,scan:=scan,publicBody:=publicBody,
    publicRead:=publicRead,publicBorrow:=publicBorrow,publicCellRead:=publicCellRead,
    publicClone:=publicClone,decodedBody:=decodedBody,decoded:=decoded,
    statementBody:=statementBody,validated:=validated,encoded:=encoded,proofBody:=proofBody,
    proofRead:=proofRead,cpReadAtProof:=cpReadAtProof,proofBorrow:=proofBorrow,
    proofCellRead:=proofCellRead,proofClone:=proofClone,gate:=gate,splitRead:=splitRead,
    splitCast:=splitCast,firstBody:=firstBody,range:=range,firstReturned:=firstReturned,
    copyBody:=copyBody,copyCellRead:=copyCellRead,length:=length,copied:=copied,
    checkpointDrop:=checkpointDrop,proofDrop:=proofDrop,statementDrop:=statementDrop,
    publicDrop:=publicDrop,cpDrop:=cpDrop }⟩

#print axioms reference_certificate
end AspisR1.S2E
