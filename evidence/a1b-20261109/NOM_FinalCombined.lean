import NOM_TerminalDomain
import NOM_MerkleGuard
import NOM_MerkleVerify
import NOM_MerkleLoop
import NOM_MerkleParent
import NOC_FinishSource
import NOC_Op9Slot
import NOC_Op9
import NOC_MerkleBounded
import NOC_PrepareDiv
import NOC_Run5bHost
import NOC_PrepareFront
import NOC_ReadTransport
import NOC_QueryLink
import NOC_QueryDomain
import NOC_ConvLeaves
import NOC_ConvSemantic
import NOC_Conv094
set_option autoImplicit false
noncomputable section
namespace AspisR1.NOM_FinalCombined
open Aeneas Aeneas.Std Result
/-- Delivered (M) type, exactly the open converse of NOC_HANDOFF (k = 0 at the host). -/
example {W Tx : Type} (c : NNH_Run5bCtx.Ctx W Tx) (a : LIBC_BatchMerkle.Args)
 (domain : LIBC_BatchMerkle.Domain a) :
 Port4B_Install.batch (Tx1Q_Install.digest (NNV_PreparedAtHost.digest c)) (LIBC_Bytes.raw a.1)
  (LIBC_BatchMerkle.prepared a) (LIBC_BatchMerkle.folded a) 0#usize ()=ok (.Ok ()) →
 NHT_ResultPort.action (LIBC_BatchMerkle.model a (NNH_Run5bCtx.envOf c))=ok (.Ok ()) :=
 NOM_MerkleParent.model0 c a domain
/-- Delivered (M) type at the NKV action (NOC_HANDOFF open goal 2). -/
example (H : AspisV8R19.DuplexFrames.Bytes → AspisV8R19.SourceDuplexStep.State)
 (D : VTop_Stages.aspis_core.digest.Digest32 Unit) (agree : NOC_MerkleBounded.NodeLeaf D H)
 (proof : Slice U8) (p : VTop_Stages.verifier.Prepared) (folded : Array U8 32#usize)
 (q : ∀ j,j<22 → p.queries.val[j]!.val<262144) :
 Port4B_Install.batch D proof p folded 0#usize ()=ok (.Ok ()) →
 NHT_ResultPort.action (NKV_FRef.verifier.candidate.batch_merkle
  (NKV_ConcreteChildren.ops H) (NKV_ConcreteChildren.digest H) proof p folded 0#usize ())=ok (.Ok ()) :=
 NOM_MerkleParent.parent H D agree proof p folded 0#usize (by decide) q
/-- Delivered (T) type: digest half on the reached 345 path. -/
example (st : NNH_S1HostCodec.Statement) :
 NNH_S1HostCodec.validate st = .ok (.Ok ()) →
 LIB_VPublicDomain.publicDigestDom (NNH_Libraries.C.semanticPublic (NNH_S1DecodeOk.carrier st)) :=
 NOM_TerminalDomain.validated_digest st
#print axioms AspisR1.NOM_TerminalDomain.validate_native
#print axioms AspisR1.NOM_TerminalDomain.validate_iff
#print axioms AspisR1.NOM_TerminalDomain.validated_digest
#print axioms AspisR1.NOM_TerminalDomain.library_digest
#print axioms AspisR1.NOM_TerminalDomain.asset
#print axioms AspisR1.NOM_TerminalDomain.domain
#print axioms AspisR1.NOM_TerminalDomain.reached
#print axioms AspisR1.NOM_TerminalDomain.terminal
#print axioms AspisR1.NOM_MerkleGuard.scan
#print axioms AspisR1.NOM_MerkleGuard.well
#print axioms AspisR1.NOM_MerkleGuard.aligned
#print axioms AspisR1.NOM_MerkleGuard.guards
#print axioms AspisR1.NOM_MerkleVerify.reset
#print axioms AspisR1.NOM_MerkleVerify.endpoint
#print axioms AspisR1.NOM_MerkleVerify.verify
#print axioms AspisR1.NOM_MerkleLoop.terminal
#print axioms AspisR1.NOM_MerkleLoop.loop
#print axioms AspisR1.NOM_MerkleParent.treeCode
#print axioms AspisR1.NOM_MerkleParent.tree
#print axioms AspisR1.NOM_MerkleParent.values
#print axioms AspisR1.NOM_MerkleParent.parent
#print axioms AspisR1.NOM_MerkleParent.parent_iff
#print axioms AspisR1.NOM_MerkleParent.hostParent
#print axioms AspisR1.NOM_MerkleParent.model0
#print axioms AspisR1.NOM_MerkleParent.model0_iff
#print axioms AspisR1.NOC_FinishSource.step
#print axioms AspisR1.NOC_FinishSource.source
#print axioms AspisR1.NOC_Op9Slot.slot
#print axioms AspisR1.NOC_Op9Slot.digest
#print axioms AspisR1.NOC_Op9Slot.pub_round
#print axioms AspisR1.NOC_Op9Slot.reservation
#print axioms AspisR1.NOC_Op9Slot.prefix_finish
#print axioms AspisR1.NOC_Op9.op9
#print axioms AspisR1.NOC_MerkleBounded.node
#print axioms AspisR1.NOC_MerkleBounded.leaf
#print axioms AspisR1.NOC_MerkleBounded.rows
#print axioms AspisR1.NOC_MerkleBounded.level
#print axioms AspisR1.NOC_MerkleBounded.iterate
#print axioms AspisR1.NOC_MerkleBounded.height
#print axioms AspisR1.NOC_MerkleBounded.endpoint
#print axioms AspisR1.NOC_MerkleBounded.verify
#print axioms AspisR1.NOC_MerkleBounded.terminal
#print axioms AspisR1.NOC_MerkleBounded.active
#print axioms AspisR1.NOC_MerkleBounded.loop
#print axioms AspisR1.NOC_MerkleBounded.treeCode
#print axioms AspisR1.NOC_MerkleBounded.tree
#print axioms AspisR1.NOC_MerkleBounded.values
#print axioms AspisR1.NOC_MerkleBounded.parent
#print axioms AspisR1.NOC_MerkleBounded.hostNode
#print axioms AspisR1.NOC_MerkleBounded.host
#print axioms AspisR1.NOC_MerkleBounded.hostParent
#print axioms AspisR1.NOC_MerkleBounded.model0
#print axioms AspisR1.NOC_PrepareDiv.op1_div
#print axioms AspisR1.NOC_PrepareDiv.logical_semantic
#print axioms AspisR1.NOC_PrepareDiv.logical_y1
#print axioms AspisR1.NOC_PrepareDiv.logical_sum
#print axioms AspisR1.NOC_PrepareDiv.prepare_div
#print axioms AspisR1.NOC_HostSeed.filled
#print axioms AspisR1.NOC_HostSeed.m0
#print axioms AspisR1.NOC_HostSeed.diff
#print axioms AspisR1.NOC_HostSeed.op1_slot
#print axioms AspisR1.NOC_HostCtx.exhibited
#print axioms AspisR1.NOC_HostCtx.extraction
#print axioms AspisR1.NOC_Run5bHost.S_host
#print axioms AspisR1.NOC_Run5bHost.a0
#print axioms AspisR1.NOC_Run5bHost.r0
#print axioms AspisR1.NOC_SeedTransfer.config
#print axioms AspisR1.NOC_SeedTransfer.currentBase
#print axioms AspisR1.NOC_SeedTransfer.current
#print axioms AspisR1.NOC_SeedTransfer.current_op1
#print axioms AspisR1.NOC_SeedTransfer.stage
#print axioms AspisR1.NOC_SeedTransfer.sdk
#print axioms AspisR1.NOC_SeedTransfer.digest
#print axioms AspisR1.NOC_SeedTransfer.op9
#print axioms AspisR1.NOC_PrepareFront.filled
#print axioms AspisR1.NOC_PrepareFront.off_y1
#print axioms AspisR1.NOC_PrepareFront.off_inactive
#print axioms AspisR1.NOC_PrepareFront.window
#print axioms AspisR1.NOC_PrepareFront.values_congr
#print axioms AspisR1.NOC_PrepareFront.values
#print axioms AspisR1.NOC_PrepareFront.recombined
#print axioms AspisR1.NOC_PrepareFront.source
#print axioms AspisR1.NOC_ReadTransport.wmul
#print axioms AspisR1.NOC_ReadTransport.wadd
#print axioms AspisR1.NOC_ReadTransport.start
#print axioms AspisR1.NOC_ReadTransport.finish
#print axioms AspisR1.NOC_ReadTransport.read
#print axioms AspisR1.NOC_QueryLink.call_eq
#print axioms AspisR1.NOC_QueryLink.loop_eq
#print axioms AspisR1.NOC_QueryLink.closure_eq
#print axioms AspisR1.NOC_QueryLink.values_eq
#print axioms AspisR1.NOC_QueryLink.loop
#print axioms AspisR1.NOC_QueryLink.link
#print axioms AspisR1.NOC_QueryLink.current
#print axioms AspisR1.NOC_QueryDomain.graphRet
#print axioms AspisR1.NOC_QueryDomain.prepared
#print axioms AspisR1.NOC_QueryDomain.domain
#print axioms AspisR1.NOC_ConvLeaves.filled
#print axioms AspisR1.NOC_ConvLeaves.filled_value
#print axioms AspisR1.NOC_ConvLeaves.expand_semantic
#print axioms AspisR1.NOC_ConvLeaves.expand_values
#print axioms AspisR1.NOC_ConvLeaves.parse
#print axioms AspisR1.NOC_ConvLeaves.view
#print axioms AspisR1.NOC_ConvLeaves.prepared
#print axioms AspisR1.NOC_ConvSemantic.transcript
#print axioms AspisR1.NOC_ConvSemantic.parse
#print axioms AspisR1.NOC_ConvSemantic.begin_
#print axioms AspisR1.NOC_ConvSemantic.rounds
#print axioms AspisR1.NOC_ConvSemantic.circle
#print axioms AspisR1.NOC_ConvSemantic.record
#print axioms AspisR1.NOC_ConvSemantic.decode
#print axioms AspisR1.NOC_ConvSemantic.payload
#print axioms AspisR1.NOC_ConvSemantic.claims
#print axioms AspisR1.NOC_Conv094.scan
#print axioms AspisR1.NOC_Conv094.geometry
#print axioms AspisR1.NOC_Conv094.accNew
#print axioms AspisR1.NOC_Conv094.weightsNew
end AspisR1.NOM_FinalCombined
end
