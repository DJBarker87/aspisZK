import RPt_FJp_PhaseReady
import RPt_FJp_NativeFirst
import RPt_FJp_NativeReader
import RPt_FJp_ObservedMatch
import RPt_FJo_ReaderLiteralPowers
import RPt_FJo_GeometryInverses
import RPt_FJo_QueryRaw
import RPt_FJl_LoopExtraction
import RPz7_Cons_NativeBuild
import RPz8_F3Y_InstalledLaws
set_option autoImplicit false
noncomputable section
namespace AspisR1.FJp_NativePair
open Aeneas Aeneas.Std Result
open AspisR1CurrentCaller InstalledPreparation
open AspisR1Stage2
open AspisV8R19.DuplexFrames
/-- Original native operands; the powers call is retained by NativeBuilder.
Recovery remains a local branch result, never an owner field. -/
theorem value {C Hash : Type} (err : C) (seed : DrvC_Installation.Configuration FIo_Install.W C)
    (r : NP6_StdModel.Reservation) (ops : Ops)
    (B : AspisR1PublicPreparation.FinishModel.Boundaries) (std : ClaimsUnrolledFinish.StdCalls)
    (D : AspisR1CurrentCaller.aspis_core.digest.Digest32 Hash) (hash : Hash)
    (pub : AspisR1CurrentCaller.aspis_statement.pool_v1.pair_forest_semantic_terminal.r0.Public)
    (publicBytes proof : Slice U8) (split : Usize) (saved : alloc.vec.Vec U8)
    (run : Tx1Q_Execution.Run
      (Tx1Q_Execution.actual ops (FIp_Install.configuration err seed r).reserved
        (FIp_Install.configuration err seed r).query (FIp_Install.configuration err seed r).geometry B std)
      (FIp_Install.configuration err seed r).reserved (FIp_Install.configuration err seed r).query
      (FIp_Install.configuration err seed r).geometry D hash pub publicBytes proof split saved)
    (checkpoint proof1 pub1 : Slice U8) (t : Cons_Native.Witness)
    (aux : Cons_NativeBuild.Aux (FIp_Install.configuration err seed r).reserved
      (FIp_Install.configuration err seed r).query (FIp_Install.configuration err seed r).geometry
      (Tx1Q_Install.digest D) hash pub1 proof1 checkpoint t)
    (powersCall : Tx2N_Powers.powers 29#usize t.p2.gamma=ok t.g2)
    (sameSaved : MultiproofConeCanonical.bytesOf checkpoint.val=MultiproofConeCanonical.bytesOf saved.val)
    (sameProof : MultiproofConeCanonical.bytesOf proof1.val=MultiproofConeCanonical.bytesOf proof.val)
    (size : proof.val.length=57607)
    (out : AspisR1PublicPreparation.verifier.Prepared)
    (parsed : OraclePortCompactDraft.Parsed) (view : LiteralOpeningView.View)
    (q : Fin 22 → Fin 262144) (tr : RawCutTranscriptRun.ErasedPrefix)
    (data : RecordedBinaryExperimentBin.SourceInputs)
    (same : currentPrepared out=run.p)
    (numeric : F3L_SourcePrepared.numeric out=OraclePortCheckpointResumeC5.prepared
      (OraclePortAcceptedContextC6.context parsed data view) data.data (SelectedChallengeMap.rhoOf data.rho) q)
    (prepare : Port5Q1_QueryPorts.SessionAPrepare (Tx1Q_Carriers.prepared run.p) data.data q (SelectedChallengeMap.rhoOf data.rho))
    (read : LiteralMatchingData.read (OraclePortStoredDecisionDraftC4.typedRows parsed q tr)=some data.data)
    (queries : OraclePortSelectedDraft.queries tr=some q)
    (wire : parsed.wire=MultiproofConeCanonical.bytesOf proof.val)
    (recovered : Nat → Option Bytes)
    (authenticated : ∀ pos,pos<22 → recovered (OraclePortSelectedDraft.index q 2 pos)=some (OraclePortPackedChoiceC4.payload parsed 2 pos)) :
    ∀ j : Fin 22,MatchingSupport.match0 data.data (q j) := by
  let c := FIp_Install.configuration err seed r
  have first := FJp_NativeFirst.value ops c.reserved c.query c.geometry B std D hash pub publicBytes proof split saved run out parsed view q data same numeric
  have canonical := FJo_Tx1GammaCanonical.value ops c.reserved c.query c.geometry B std D hash pub publicBytes proof split saved run
  have second := FJo_ReaderLiteralPowers.value c.stageBase c.reserved (Tx1Q_Install.digest D) hash
    checkpoint proof publicBytes proof1 pub1 saved (Tx1Q_Carriers.prepared run.p) t.p2
    (Tx1Q_Carriers.accumulator {run.out with weights:=⟨run.flushed.val,run.flushed.property⟩}) t.saved2
    t.g2 data.data.gamma canonical run.writer_call sameSaved aux.1 powersCall first.2.2.1
  have source := Port4A_ReaderInstall.accepted_source c.stageBase c.reserved (Tx1Q_Install.digest D) hash
    checkpoint proof1 pub1 .S2 t.p2 t.saved2 aux.1
  have fields := SdkD_CheckpointBinding.fields c.reserved (Tx1Q_Install.digest D)
    (Tx1Q_Carriers.prepared run.p) t.p2
    (Tx1Q_Carriers.accumulator {run.out with weights:=⟨run.flushed.val,run.flushed.property⟩}) t.saved2
    checkpoint proof publicBytes proof1 pub1 hash saved run.writer_call sameSaved source
  have geom0 := Port5Q1_GeometryReads.accepted c.geometry
    (F3Y_InstalledLaws.canonical err (FIo_Install.select r seed) r)
    (F3Y_InstalledLaws.domain err (FIo_Install.select r seed) r)
    (F3Y_InstalledLaws.multiply err (FIo_Install.select r seed) r)
    (F3Y_InstalledLaws.one err (FIo_Install.select r seed) r)
    (F3Y_InstalledLaws.inverse err (FIo_Install.select r seed) r)
    run.p.queries 0#usize 10#usize (Tx1Q_Carriers.geometry run.geometry) (by decide) run.geometry_call
  have geoCall := aux.2.2.1
  rw [aux.2.1] at geoCall
  have geom1 := Port5Q1_GeometryReads.accepted c.geometry
    (F3Y_InstalledLaws.canonical err (FIo_Install.select r seed) r)
    (F3Y_InstalledLaws.domain err (FIo_Install.select r seed) r)
    (F3Y_InstalledLaws.multiply err (FIo_Install.select r seed) r)
    (F3Y_InstalledLaws.one err (FIo_Install.select r seed) r)
    (F3Y_InstalledLaws.inverse err (FIo_Install.select r seed) r)
    t.p2.queries 10#usize 22#usize t.geometry2 (by decide) geoCall
  have size1 : proof1.val.length=57607 := by
    have h := congrArg List.length sameProof
    simpa only [MultiproofConeCanonical.bytesOf,List.length_map,size] using h
  intro j
  by_cases early : j.val<10
  · obtain ⟨a0,a1,b0,b1,index,called⟩ := FJl_Tx1Extraction.reached _ c.reserved c.query c.geometry D hash pub publicBytes proof split saved run ⟨j.val,early⟩
    obtain ⟨o⟩ := Port4C_QueryValues.observed _ proof _ a0 a1 _ none _ b0 b1 called
    have raw : (Port5Q1_GeometryBinding.queryAt (Tx1Q_Carriers.prepared run.p).queries a0.next.val).val=(q j).val := by
      rw [index];exact prepare.queries j.val j.isLt
    have inv := FJo_GeometryInverses.value (E:=AspisWideTower.WideExact)
      (Tx1Q_Carriers.prepared run.p).queries 0#usize 10#usize _ geom0 a0.next
      (by scalar_tac) (by rw [index];exact early) o.inverse o.z o.inverse_read o.z_read (q j) raw
    have alpha := first.2.2.2 o.alpha0 o.alpha0_read
    have ix := inv.1
    have iy := inv.2
    let normalized := FJp_PhaseReady.early err seed r proof _ a0 a1 _ _ b0 b1 o
    with_reducible exact (FJp_ObservedMatch.value err seed r true proof (Tx1Q_Carriers.prepared run.p) a0 a1
      (Tx1Q_Carriers.arr Tx1Q_Carriers.e run.scratch) (Tx1Q_Carriers.geometry run.geometry) b0 b1 normalized parsed q tr data.data
      read queries wire size j index first.1 first.2.1 alpha
      ix iy recovered authenticated raw)
  · obtain ⟨a0,a1,b0,b1,index,called⟩ := FJl_LoopExtraction.installed _ proof1 t.p2 t.saved2 t.returned2 t.g2 t.geometry2 t.pending2 t.after2 22#usize
      (by rw [aux.2.1];decide) aux.2.2.2.2.1 j.val (by rw [aux.2.1];exact Nat.le_of_not_gt early) j.isLt
    obtain ⟨o⟩ := Port4C_QueryValues.observed _ proof1 _ a0 a1 _ none _ b0 b1 called
    have raw : (Port5Q1_GeometryBinding.queryAt t.p2.queries a0.next.val).val=(q j).val := by
      rw [index,fields.2.2];exact prepare.queries j.val j.isLt
    have inv := FJo_GeometryInverses.value (E:=AspisWideTower.WideExact)
      t.p2.queries 10#usize 22#usize _ geom1 a0.next
      (by rw [index];exact Nat.le_of_not_gt early) (by rw [index];exact j.isLt)
      o.inverse o.z o.inverse_read o.z_read (q j) raw
    have alpha := FJp_NativeReader.alpha ops c.reserved c.query c.geometry B std c.stageBase D hash pub publicBytes proof split saved run
      checkpoint proof1 pub1 t.p2 t.saved2 sameSaved aux.1 data.data.alpha0 first.2.2.2 o.alpha0 o.alpha0_read
    have ix := inv.1
    have iy := inv.2
    let normalized := FJp_PhaseReady.late err seed r proof1 t.p2 a0 a1 t.g2 t.geometry2 b0 b1 o
    with_reducible exact (FJp_ObservedMatch.value err seed r false proof1 t.p2 a0 a1 t.g2 t.geometry2 b0 b1 normalized parsed q tr data.data
      read queries (wire.trans sameProof.symm) size1 j index second.1 second.2 alpha ix iy recovered authenticated raw)
#print axioms value
end AspisR1.FJp_NativePair
end
