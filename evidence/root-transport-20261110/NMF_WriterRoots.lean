import RPz7_SdkD_PhysicalRoots
import RPz7_SdkD_WriterRoots
import NLW_WriterRoot0
import NLW_ByteIdentity
import NLP_InputDomain
set_option autoImplicit false
noncomputable section
namespace NMF_WriterRoots
open Aeneas Aeneas.Std Result AspisR1
open AspisV8R19.DuplexFrames AspisV8R19.SourceDuplexStep AspisV8R19.SqueezeOracleBridge
open MultiproofConeCanonical
/-- The first root of the actual accepted preparation, before serialization. -/
theorem physical {C X : Type} (ops : AspisR1CurrentCaller.Ops) (reserved : Bool)
 (query : Port3_NativeQueryBody.Ops) (geo : Port3_NativeGeometryBody.Ops C)
 (B : AspisR1PublicPreparation.FinishModel.Boundaries) (std : ClaimsUnrolledFinish.StdCalls)
 (D : AspisR1CurrentCaller.aspis_core.digest.Digest32 X) (hash : X)
 (semantic : AspisR1CurrentCaller.aspis_statement.pool_v1.pair_forest_semantic_terminal.r0.Public)
 (pub proof : Slice U8) (split : Usize) (saved : alloc.vec.Vec U8)
 (run : Tx1Q_Execution.Run (Tx1Q_Execution.actual ops reserved query geo B std)
   reserved query geo D hash semantic pub proof split saved) :
 Port3_BatchStage.root0 (Tx1Q_Carriers.prepared run.p)=encodeState
   ((SemanticRecordCodec.decodeState (OraclePortCompactDraft.slice (bytesOf proof.val) 16 32)).getD (fun _=>0)) := by
 have call := run.prepare_call
 change AspisR1CurrentCaller.verifier.candidate.prepare
   (RowShape_InstalledSlots.verifierOps (Tx1Q_SameCut.dictionary ops reserved query geo) B std)
   D semantic proof hash none (Array.repeat 29#usize run.zero)=ok (.Ok run.p,run.scratch) at call
 obtain ⟨r0,r1,roots,first,second⟩:=SdkD_PhysicalRoots.prepared
   (Tx1Q_SameCut.dictionary ops reserved query geo) B std D semantic proof hash run.p _ _ call
 have bytes : bytesOf r0.val=OraclePortCompactDraft.slice (bytesOf proof.val) 16 32 := by
   rw [first,SdkD_ModelRoots.rawSlice]
 have eq : Port3_BatchStage.root0 (Tx1Q_Carriers.prepared run.p)=r0 := by
   simp only [Port3_BatchStage.root0,Tx1Q_Carriers.prepared,roots,Array.make]
   rfl
 rw [eq,←bytes,SdkD_ModelRoots.decode_native,Option.getD_some,array_roundtrip]

/-- The actual writer preserves the accepted preparation's root bytes.
No total-digest, injectivity, size or canonicality hypothesis is needed. -/
theorem serialized {X : Type} (D : VTop_Stages.aspis_core.digest.Digest32 X) (hash : X)
 (p : AspisR1Stage2.verifier.Prepared) (a : AspisR1Stage2.verifier.Accumulator)
 (proof pub : Slice U8) (saved : alloc.vec.Vec U8)
 (success : Port3_CheckpointInstall.writer D p a proof pub hash=ok saved)
 (root : Port3_BatchStage.root0 p=encodeState
   ((SemanticRecordCodec.decodeState (OraclePortCompactDraft.slice (bytesOf proof.val) 16 32)).getD (fun _=>0))) :
 NLP_InputDomain.Root0 saved.deref proof := by
 apply NLW_ByteIdentity.bytes_injective
 change bytesOf ((saved.val.drop 112).take 32)=_
 simpa only [bytesOf,OraclePortCompactDraft.slice,List.map_take,List.map_drop] using
   (SdkD_WriterRoots.returned D p a proof pub hash saved success).1.trans
     (congrArg (fun r : Array U8 32#usize => bytesOf r.val) root)
#print physical
#print serialized
#print axioms physical
#print axioms serialized
end NMF_WriterRoots
