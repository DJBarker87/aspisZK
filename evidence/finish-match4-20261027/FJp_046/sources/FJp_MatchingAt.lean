import FJp_PhaseReady
import FJp_ObservedMatch
import FJo_PairSource
import FJo_PairPowers
import FJo_ReaderLiteralAlpha
import FJo_ReaderQueriesAt
import FJo_Tx1Geometry
import FJo_GeometryInverses
import FJo_RecoveryAt
import F3V_EvidenceCalls
set_option autoImplicit false
noncomputable section
namespace AspisR1.FJp_MatchingAt
open Aeneas Aeneas.Std Result AspisR1Stage2
open DrvC_Installation F3V_RunEvidence Tx1Q_Carriers
open AspisV8R19.DuplexFrames AspisV8R19.SourceDuplexStep
open AspisV8R19.MemoizedProgramLaw
/-- SAME-run matching OR the existing collision, without a matching owner law. -/
theorem value {C : Type} (err : C) (seed : Configuration FIo_Install.W C) (r : NP6_StdModel.Reservation)
    (B : AspisR1PublicPreparation.FinishModel.Boundaries) (s : F3T_ByteCarrier.Submission)
    (H : Bytes → State) (e : Evidence (FIp_Install.configuration err seed r) B s H)
    (i : F3_Model.Input) (p : OraclePortCompactDraft.Parsed) (q : Fin 22 → Fin 262144)
    (data : RecordedBinaryExperimentBin.SourceInputs)
    (atPrepared : FGl_PreparedAt.At (FIp_Install.configuration err seed r) B s H e i p q data)
    (prior : Program Bytes State Unit) :
    let c := FIp_Install.configuration err seed r
    let trace := (eval H prior).1 ++ AuS1_Recovery.log
      (Uni_Install.current c.currentBase c.reserved c.query c.geometry) c.boundaries c.std (D1 c H)
      (AspisS6CurrentVerifierCarrier.toPublic e.semantic) e.proof () (Array.repeat 29#usize e.run.zero)
    AuS1_Finish.Collision H trace p q ∨ ∀ j : Fin 22,MatchingSupport.match0 data.data (q j) := by
  let c := FIp_Install.configuration err seed r
  obtain ⟨frame,frameRead,target,recovery⟩ := FJo_RecoveryAt.value c B s H e i p q data atPrepared prior
  rcases recovery with collision | authenticated
  · exact Or.inl collision
  right
  obtain ⟨p2,saved2,g2,geo2,hr,hn,hg,hgeo,calls⟩ := FJo_PairSource.value c B s H e
  have first := FJo_Tx1AtPowers.value c B s H e i p q data atPrepared
  have canonical := FJo_Tx1GammaCanonical.value (Op5T_Concrete.current c.currentBase) c.reserved c.query c.geometry
    c.boundaries c.std (D1 c H) () (AspisS6CurrentVerifierCarrier.toPublic e.semantic) e.pub e.proof 10#usize e.saved e.run
  have write : Port3_CheckpointInstall.writer (D2 c H) (prepared e.run.p)
      (accumulator {e.run.out with weights:=⟨e.run.flushed.val,e.run.flushed.property⟩}) e.proof e.pub ()=ok e.saved := e.run.writer_call
  have second := FJo_ReaderLiteralPowers.value c.stageBase c.reserved (D2 c H) ()
    e.saved.deref e.proof e.pub e.proof e.pub e.saved (prepared e.run.p) p2
    (accumulator {e.run.out with weights:=⟨e.run.flushed.val,e.run.flushed.property⟩}) saved2
    g2 data.data.gamma canonical write rfl hr hg (FJl_PreparedAtValues.value c B s H e i p q data atPrepared).1
  have geom0 := FJo_Tx1Geometry.value err seed r B s H e
  have geom1 := Port5Q1_GeometryReads.accepted c.geometry
    (F3Y_InstalledLaws.canonical err (FIo_Install.select r seed) r)
    (F3Y_InstalledLaws.domain err (FIo_Install.select r seed) r)
    (F3Y_InstalledLaws.multiply err (FIo_Install.select r seed) r)
    (F3Y_InstalledLaws.one err (FIo_Install.select r seed) r)
    (F3Y_InstalledLaws.inverse err (FIo_Install.select r seed) r)
    p2.queries 10#usize 22#usize geo2 (by decide) hgeo
  have wire := (OraclePortStoredParserC4.parsed i.stored _ p atPrepared.2.2.1).2.1.trans atPrepared.2.1
  have read := (OraclePortStoredDecisionDraftC4.input_fields p q _ data atPrepared.2.2.2.2.1).2
  have size := F3V_EvidenceCalls.length c B s H e
  have hqueries := atPrepared.2.2.2.1
  have firstAlpha := (FJl_PreparedAtValues.value c B s H e i p q data atPrepared).2
  intro j
  obtain ⟨a0,a1,b0,b1,index,called⟩ := calls j
  by_cases early : j.val<10
  · simp only [if_pos early] at called
    obtain ⟨o⟩ := Port4C_QueryValues.observed _ e.proof _ a0 a1 _ none _ b0 b1 called
    have raw : (Port5Q1_GeometryBinding.queryAt (prepared e.run.p).queries a0.next.val).val=(q j).val := by
      rw [index];exact atPrepared.2.2.2.2.2.1.queries j.val j.isLt
    have inverse := FJo_GeometryInverses.value (E:=AspisWideTower.WideExact) (prepared e.run.p).queries 0#usize 10#usize
      (geometry e.run.geometry) geom0 a0.next (by scalar_tac)
      (by rw [index];exact early) o.inverse o.z o.inverse_read o.z_read (q j) raw
    have alpha := firstAlpha o.alpha0 o.alpha0_read
    have ix := inverse.1
    have iy := inverse.2
    let normalized := FJp_PhaseReady.early err seed r e.proof _ a0 a1 _ _ b0 b1 o
    with_reducible exact (FJp_ObservedMatch.value err seed r true e.proof (prepared e.run.p) a0 a1 (arr Tx1Q_Carriers.e e.run.scratch) (geometry e.run.geometry) b0 b1 normalized p q _ data.data read
      hqueries wire size j index first.1 first.2 alpha
      ix iy _ authenticated raw)
  · simp only [if_neg early] at called
    obtain ⟨o⟩ := Port4C_QueryValues.observed _ e.proof _ a0 a1 _ none _ b0 b1 called
    have raw : (Port5Q1_GeometryBinding.queryAt p2.queries a0.next.val).val=(q j).val := by
      rw [index];exact FJo_ReaderQueriesAt.value c B s H e i p q data atPrepared p2 saved2 hr j
    have inverse := FJo_GeometryInverses.value (E:=AspisWideTower.WideExact) p2.queries 10#usize 22#usize geo2 geom1 a0.next
      (by rw [index];exact Nat.le_of_not_gt early) (by rw [index];exact j.isLt)
      o.inverse o.z o.inverse_read o.z_read (q j) raw
    have alpha := FJo_ReaderLiteralAlpha.value c B s H e i p q data atPrepared p2 saved2 hr o.alpha0 o.alpha0_read
    have ix := inverse.1
    have iy := inverse.2
    let normalized := FJp_PhaseReady.late err seed r e.proof p2 a0 a1 g2 geo2 b0 b1 o
    with_reducible exact (FJp_ObservedMatch.value err seed r false e.proof p2 a0 a1 g2 geo2 b0 b1 normalized p q _ data.data read
      hqueries wire size j index second.1 second.2 alpha
      ix iy _ authenticated raw)
#print axioms value
end AspisR1.FJp_MatchingAt
end
