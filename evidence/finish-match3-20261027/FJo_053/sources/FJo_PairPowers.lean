import FJo_ReaderLiteralPowers
import FJo_Tx1AtPowers
import FJo_Tx1GammaCanonical
import FJl_PairExtraction
set_option autoImplicit false
noncomputable section
namespace AspisR1.FJo_PairPowers
open Aeneas Aeneas.Std Result AspisR1Stage2
open DrvC_Installation F3V_RunEvidence Tx1Q_Carriers
open AspisV8R19.DuplexFrames AspisV8R19.SourceDuplexStep
/-- Both actual arrays are powers of the SAME literal gamma; all iterations
come from the SAME accepted pair, with no supplied resumed-field law. -/
theorem value {F C : Type} (c : Configuration F C)
    (B : AspisR1PublicPreparation.FinishModel.Boundaries) (s : F3T_ByteCarrier.Submission)
    (H : Bytes → State) (e : Evidence c B s H) (i : F3_Model.Input)
    (p : OraclePortCompactDraft.Parsed) (q : Fin 22 → Fin 262144)
    (data : RecordedBinaryExperimentBin.SourceInputs)
    (atPrepared : FGl_PreparedAt.At c B s H e i p q data) :
    ∃ (p2 : verifier.Prepared) (saved2 : verifier.Accumulator)
      (g2 : Array FIp_DotsAdapter.E 29#usize) (geo2 : verifier.QueryGeometry),
      Port4A_ReaderInstall.reader c.reserved (D2 c H) e.saved.deref e.proof e.pub .S2 ()=ok (.Ok (p2,saved2)) ∧
      saved2.next=10#usize ∧ Tx2N_Powers.powers 29#usize p2.gamma=ok g2 ∧
      ∀ j : Fin 22,
        (let g := FIp_DotsAdapter.toArray (if j.val<10 then arr Tx1Q_Carriers.e e.run.scratch else g2)
         FIo_ArrayCanon.Holds g ∧ ∀ l : Fin 29,FIp_ArrayValue.value g l.val=data.data.gamma^l.val) ∧
        ∃ a0 a1 b0 b1,a0.next.val=j.val ∧
          Port3_NativeQueryBody.verifier.candidate.query_values
            (if j.val<10 then Tx1Q_QueryBridge.leaves c.query else
              Port3_QueryStage.release (Port4C_RowStd.install (Port5Q1_QueryPorts.install c.query)))
            e.proof (if j.val<10 then prepared e.run.p else p2) a0
            (if j.val<10 then arr Tx1Q_Carriers.e e.run.scratch else g2) none
            (if j.val<10 then geometry e.run.geometry else geo2) b0=ok (.Ok (a1,b1)) := by
  obtain ⟨p2,saved2,g2,geo2,hr,hn,hg,calls⟩ := FJl_PairExtraction.accepted c B s H e
  have first := FJo_Tx1AtPowers.value c B s H e i p q data atPrepared
  have canonical := FJo_Tx1GammaCanonical.value (Op5T_Concrete.current c.currentBase) c.reserved c.query c.geometry
    c.boundaries c.std (D1 c H) () (AspisS6CurrentVerifierCarrier.toPublic e.semantic) e.pub e.proof 10#usize e.saved e.run
  have write : Port3_CheckpointInstall.writer (D2 c H) (prepared e.run.p)
      (accumulator {e.run.out with weights:=⟨e.run.flushed.val,e.run.flushed.property⟩}) e.proof e.pub ()=ok e.saved := e.run.writer_call
  have second := FJo_ReaderLiteralPowers.value c.stageBase c.reserved (D2 c H) ()
    e.saved.deref e.proof e.pub e.proof e.pub e.saved (prepared e.run.p) p2
    (accumulator {e.run.out with weights:=⟨e.run.flushed.val,e.run.flushed.property⟩}) saved2
    g2 data.data.gamma canonical write rfl hr hg (FJl_PreparedAtValues.value c B s H e i p q data atPrepared).1
  refine ⟨p2,saved2,g2,geo2,hr,hn,hg,?_⟩
  intro j
  refine ⟨?_,calls j⟩
  by_cases early : j.val<10
  · simpa only [if_pos early] using first
  · simpa only [if_neg early] using second
#print axioms value
end AspisR1.FJo_PairPowers
end
