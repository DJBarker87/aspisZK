import FJo_ObservationMeaning
import FJo_PairPowers
import FIp_Install
set_option autoImplicit false
noncomputable section
namespace AspisR1.FJo_PairDots
open Aeneas Aeneas.Std Result AspisR1Stage2
open DrvC_Installation F3V_RunEvidence Tx1Q_Carriers
open AspisV8R19.DuplexFrames AspisV8R19.SourceDuplexStep
/-- All 22 complete literal batched values from ONE original owner context. -/
theorem value {C : Type} (err : C) (seed : Configuration FIo_Install.W C) (r : NP6_StdModel.Reservation)
    (B : AspisR1PublicPreparation.FinishModel.Boundaries) (s : F3T_ByteCarrier.Submission)
    (H : Bytes → State) (e : Evidence (FIp_Install.configuration err seed r) B s H)
    (i : F3_Model.Input) (p : OraclePortCompactDraft.Parsed) (q : Fin 22 → Fin 262144)
    (data : RecordedBinaryExperimentBin.SourceInputs)
    (atPrepared : FGl_PreparedAt.At (FIp_Install.configuration err seed r) B s H e i p q data) :
    let c := FIp_Install.configuration err seed r
    ∃ (p2 : verifier.Prepared) (saved2 : verifier.Accumulator)
      (g2 : Array FIp_DotsAdapter.E 29#usize) (geo2 : verifier.QueryGeometry),
      Port4A_ReaderInstall.reader c.reserved (D2 c H) e.saved.deref e.proof e.pub .S2 ()=ok (.Ok (p2,saved2)) ∧
      saved2.next=10#usize ∧ Tx2N_Powers.powers 29#usize p2.gamma=ok g2 ∧
      ∀ j : Fin 22,FJo_ObservationMeaning.Holds
        (if j.val<10 then Tx1Q_QueryBridge.leaves c.query else
          Port3_QueryStage.release (Port4C_RowStd.install (Port5Q1_QueryPorts.install c.query)))
        e.proof (if j.val<10 then prepared e.run.p else p2)
        (if j.val<10 then arr Tx1Q_Carriers.e e.run.scratch else g2)
        (if j.val<10 then geometry e.run.geometry else geo2) data.data (q j) j := by
  let c := FIp_Install.configuration err seed r
  obtain ⟨p2,saved2,g2,geo2,hr,hn,hg,all⟩ := FJo_PairPowers.value c B s H e i p q data atPrepared
  have wire := (OraclePortStoredParserC4.parsed i.stored _ p atPrepared.2.2.1).2.1.trans atPrepared.2.1
  have read := (OraclePortStoredDecisionDraftC4.input_fields p q _ data atPrepared.2.2.2.2.1).2
  refine ⟨p2,saved2,g2,geo2,hr,hn,hg,?_⟩
  intro j
  obtain ⟨values,a0,a1,b0,b1,index,called⟩ := all j
  obtain ⟨o⟩ := Port4C_QueryValues.observed _ e.proof _ a0 a1 _ none _ b0 b1 called
  refine ⟨a0,a1,b0,b1,index,o,?_⟩
  exact FJo_QueryBatched.value _ e.proof _ a0 a1 _ _ b0 b1 o
    (by split <;> rfl) (by split <;> rfl) (F3V_EvidenceCalls.length c B s H e) p wire q _ data.data read
    atPrepared.2.2.2.1 j index values.1 values.2
#print axioms value
end AspisR1.FJo_PairDots
end
