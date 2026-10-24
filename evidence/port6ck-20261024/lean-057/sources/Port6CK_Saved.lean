import Port6CK_Owner
import Port6CK_Ten
import OraclePortFrozen2Checkpoint
set_option autoImplicit false
noncomputable section
namespace AspisR1.Port6CK_Saved
open Aeneas Aeneas.Std Result VTop_Stages
open AspisV8R19.DuplexFrames
open MultiproofConeCanonical OraclePortCompactDraft OraclePortSelectedDraft OraclePortStoredDecisionDraftC4
open Port5Q1_QueryPorts
open CheckpointBytes3Namespaces
variable {CoreError W : Type}
attribute [local irreducible] OraclePortCheckpointStateC3.advance OraclePortCheckpointStateC3.write
  QueryResidualBridge.values QueryResidualBridge.basis

/-- The actual CURRENT resume of ONE accepted TX1 returns Q1's saved-ten
state on the SAME bytes/Prepared/SourceInputs. The actual prefix supplies the
observation cuts and their geometry bounds. No cross-TX equality is a premise. -/
theorem accepted (base : Ops) (reserved : Bool) (panic : Port6CK_Checkpoint.Panic)
    (batch : Port3_NativeBatchBody.Ops)
    (geometryOps : Port3_NativeGeometryBody.Ops CoreError) (queryOps : Port3_NativeQueryBody.Ops)
    (finish : AspisR1Stage2.Stage2Finish.FinishOps W)
    (ports : Port6CK_Owner.SessionAPrimitives queryOps geometryOps)
    {Hsh : Type} (D : aspis_core.digest.Digest32 Hsh) (hash : Hsh) (H : Bytes → State)
    (semantic : aspis_statement.pool_v1.pair_forest_semantic_terminal.r0.Public)
    (proof pub : Slice U8) (stored publicBytes : Bytes) (split : Usize)
    (i : RecordedBinaryExperimentBin.SourceInputs) (parsed : Parsed) (q : Fin 22 → Fin 262144)
    (tr : RawCutTranscriptRun.ErasedPrefix)
    (prepare : Port6CK_Owner.SessionAPrepare base D hash semantic proof i.data q (SelectedChallengeMap.rhoOf i.rho))
    (read : LiteralMatchingData.read (typedRows parsed q tr)=some i.data)
    (wire : parsed.wire=bytesOf proof.val) (proofLength : proof.val.length=57607)
    (recovered : Nat → Option Bytes)
    (authenticated : ∀ pos, pos<22 → recovered (index q 2 pos)=some (OraclePortPackedChoiceC4.payload parsed 2 pos))
    (caller : CheckpointBytes5Join.S2S10CallerBinding (VTop_Checkpoint.digest D) hash H proof pub stored publicBytes)
    (saved : alloc.vec.Vec U8) (p1 : verifier.Prepared) (a1 : verifier.Accumulator)
    (tx1 : verifier.candidate.tx1
      (Port6CK_Checkpoint.installed base reserved panic batch geometryOps (install queryOps) finish)
      D semantic pub proof split hash none=ok (.Ok saved))
    (resumed : (Port6CK_Checkpoint.installed base reserved panic batch geometryOps (install queryOps) finish).op18 D
      (VTop_Checkpoint.checkpointSlice saved) proof pub .S2 hash=ok (.Ok (p1,a1))) :
    CheckpointBytes5Output.accumulator a1=
      (OraclePortCheckpointStateC3.write (OraclePortCheckpointResumeC5.model i.data (SelectedChallengeMap.rhoOf i.rho) q)).accumulator ∧
    a1.weights.val.length=64 ∧ a1.next.val=10 ∧
    Port4C_QueryArithmetic.CanonE a1.rhs ∧ Port3_FlushInstall.Canonical a1.power ∧
    Port5Q1_QueryPorts.SessionAPrepare p1 i.data q (SelectedChallengeMap.rhoOf i.rho) := by
  have installedPorts := Port5Q1_InstallPorts.installed queryOps ports.queryPrimitives
  obtain ⟨p,a,fields,size,canonical,reached1,wrote,sameP,sameA,next,splitEq,rest⟩ := Port6CK_Checkpoint.accepted
    base reserved panic batch geometryOps (install queryOps) finish prepare.canonical installedPorts.basis
    installedPorts.arithmetic installedPorts.line_canonical D hash H semantic proof pub stored publicBytes split
    caller saved p1 a1 tx1 resumed
  have reached := (Port6CK_Prefix.same
    (Port4C_Installed.installed base reserved batch geometryOps (install queryOps) finish)
    reserved (Port6CK_Checkpoint.unwrap panic) D hash semantic proof split p a).mp reached1
  obtain ⟨g,geometry,cuts,ten⟩ := Port6CK_Ten.reached base reserved batch geometryOps (install queryOps) finish
    prepare.canonical installedPorts.basis installedPorts.arithmetic installedPorts.line_canonical
    D hash semantic proof split p a reached
  obtain ⟨zero,hzero,hprep,hgeometry⟩ := cuts
  have prepared := prepare.model zero g p hzero hprep
  have splitValue : split=10#usize := UScalar.eq_of_val_eq splitEq
  change Port3_GeometryStage.geometry
    (Port4C_GeometryInverse.install (Port4C_CollectStd.install geometryOps)) p.queries 0#usize split=ok (.Ok geometry) at hgeometry
  rw [Port6CK_Owner.geometry_install,splitValue] at hgeometry
  have geo := Port5Q1_GeometryReads.accepted geometryOps ports.geometryPrimitives ports.domain
    ports.multiply ports.one ports.inverse p.queries 0#usize 10#usize geometry (by decide) hgeometry
  have releasePorts := Port6CK_Owner.release_ports queryOps ports.queryPrimitives
  have binding := Port6CK_Binding.from_observation (Port3_QueryStage.release queryOps) releasePorts
    proof p g (Port3_QueryInstall.observer none) geometry parsed q tr i.data (SelectedChallengeMap.rhoOf i.rho)
    prepared read wire proofLength recovered authenticated 0#usize 10#usize geo
  rw [Port6CK_Owner.release_install] at ten
  have savedTen := ten (OraclePortCheckpointResumeC5.model i.data (SelectedChallengeMap.rhoOf i.rho) q) binding
  rw [sameA,sameP]
  exact ⟨savedTen,size,next,canonical.rhs,canonical.power,prepared⟩

#print axioms accepted
end AspisR1.Port6CK_Saved
end
