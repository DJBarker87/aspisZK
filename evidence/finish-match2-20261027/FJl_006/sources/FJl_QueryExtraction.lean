import FJl_Tx1Extraction
import FJl_Tx2Extraction
import F3V_RunEvidence
set_option autoImplicit false
noncomputable section
namespace AspisR1.FJl_QueryExtraction
open Aeneas Aeneas.Std Result AspisR1Stage2
open DrvC_Installation F3V_RunEvidence Tx1Q_Carriers
open AspisV8R19.DuplexFrames AspisV8R19.SourceDuplexStep
abbrev E := aspis_core.field.wide_exact.WideExact
/-- A source call with its actual prepared, powers, geometry and cursor. -/
def At (ops : Port3_NativeQueryBody.Ops) (proof : Slice U8) (j : Nat) : Prop :=
  ∃ (p : verifier.Prepared) (g : Array E 29#usize) (geometry : verifier.QueryGeometry)
    (a0 a1 : verifier.Accumulator) (b0 b1 : verifier.BatchedWeights),
      a0.next.val=j ∧ Port3_NativeQueryBody.verifier.candidate.query_values ops
        proof p a0 g none geometry b0=ok (.Ok (a1,b1))
/-- All 22 actual loop iterations of ONE accepted two-phase byte execution.
TX1/TX2 selected arrays are preserved; equality to literal gamma powers is
not asserted by this extraction theorem. -/
theorem accepted {F C : Type} (c : Configuration F C)
    (B : AspisR1PublicPreparation.FinishModel.Boundaries)
    (s : F3T_ByteCarrier.Submission) (H : Bytes → State)
    (e : Evidence c B s H) :
    ∀ j : Fin 22, At
      (if j.val<10 then Tx1Q_QueryBridge.leaves c.query else
        Port3_QueryStage.release (Port4C_RowStd.install (Port5Q1_QueryPorts.install c.query))) e.proof j.val := by
  intro j
  by_cases first : j.val<10
  · rw [if_pos first]
    obtain ⟨a0,a1,b0,b1,hn,hcall⟩ := FJl_Tx1Extraction.reached _ c.reserved c.query c.geometry
      (D1 c H) () _ e.pub e.proof 10#usize e.saved e.run ⟨j.val,first⟩
    exact ⟨_,_,_,a0,a1,b0,b1,hn,hcall⟩
  · rw [if_neg first]
    obtain ⟨variant,shape,common⟩ := Tx2I_Cuts.authenticated_reached _ (D2 c H) ()
      e.pub e.proof e.saved.deref none e.second
    have commonRun : VTop_Stages.verifier.candidate.tx2_common
        (Tx2N_Execution.control (Tx2I_Install.stage (Op5T_Concrete.stage (AuS1_Install.base c.stageBase)) c.finish)
          c.reserved c.query c.geometry) (D2 c H) e.pub e.proof e.saved.deref () none=ok (.Ok ()) := common
    obtain ⟨p,saved,g,geometry,hr,hn,hg,calls⟩ := FJl_Tx2Extraction.reached _ c.reserved c.query c.geometry
      (D2 c H) () e.pub e.proof e.saved.deref commonRun
    have small : j.val-10<12 := by have := j.isLt; omega
    obtain ⟨a0,a1,b0,b1,hnext,hcall⟩ := calls ⟨j.val-10,small⟩
    exact ⟨p,g,geometry,a0,a1,b0,b1,by dsimp at hnext; omega,hcall⟩
#print axioms accepted
end AspisR1.FJl_QueryExtraction
end
