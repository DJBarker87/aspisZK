import FJl_ReaderPowers
import FJl_SourceSlots
set_option autoImplicit false
noncomputable section
namespace AspisR1.FJl_Tx2Values
open Aeneas Aeneas.Std Result AspisR1Stage2
open DrvC_Installation F3V_RunEvidence
open AspisV8R19.DuplexFrames AspisV8R19.SourceDuplexStep
/-- All resumed backend VALUES come from the SAME accepted execution, with
canonical powers derived from its reader and constructor, not caller inputs. -/
theorem accepted {C : Type} (err : C) (seed : Configuration FIo_Install.W C)
    (r : NP6_StdModel.Reservation) (B : AspisR1PublicPreparation.FinishModel.Boundaries)
    (s : F3T_ByteCarrier.Submission) (H : Bytes → State)
    (e : Evidence (FIp_Install.configuration err seed r) B s H) :
    ∃ (p : verifier.Prepared) (g : Array FIp_DotsAdapter.E 29#usize),
      Tx2N_Powers.powers 29#usize p.gamma=ok g ∧
      (∀ l : Fin 29,FIp_ArrayValue.value (FIp_DotsAdapter.toArray g) l.val=
        CheckpointBytes5Output.ofE p.gamma^l.val) ∧
      ∀ j : Fin 12, ∃ index : Usize,index.val=10+j.val ∧
        FJi_QueryJoin.Meaning
          (Port3_QueryStage.release (Port4C_RowStd.install (Port5Q1_QueryPorts.install
            (FIp_Install.configuration err seed r).query))) e.proof index g := by
  let c := FIp_Install.configuration err seed r
  obtain ⟨variant,shape,common⟩ := Tx2I_Cuts.authenticated_reached _ (D2 c H) ()
    e.pub e.proof e.saved.deref none e.second
  have commonRun : VTop_Stages.verifier.candidate.tx2_common
      (Tx2N_Execution.control (Tx2I_Install.stage (Op5T_Concrete.stage (AuS1_Install.base c.stageBase)) c.finish)
        c.reserved c.query c.geometry) (D2 c H) e.pub e.proof e.saved.deref () none=ok (.Ok ()) := common
  obtain ⟨p,saved,g,geometry,hr,hn,hg,calls⟩ := FJl_Tx2Extraction.reached _ c.reserved c.query c.geometry
    (D2 c H) () e.pub e.proof e.saved.deref commonRun
  have powers := FJl_ReaderPowers.value c.stageBase c.reserved (D2 c H) () e.saved.deref e.proof e.pub p saved g hr hg
  refine ⟨p,g,hg,powers.2,?_⟩
  intro j
  obtain ⟨a0,a1,b0,b1,hindex,run⟩ := calls j
  exact ⟨a0.next,hindex,FJi_QueryJoin.value _ e.proof p a0 g none geometry b0 (.Ok (a1,b1))
    (FJl_SourceSlots.installed err seed r).2.1 powers.1 run⟩
#print axioms accepted
end AspisR1.FJl_Tx2Values
end
