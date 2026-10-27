import FJo_QueryRaw
import FJo_PhaseSame
import FIp_InstalledLaws
import F3Y_InstalledLaws
import Port5Q1_CircleObservation
set_option autoImplicit false
noncomputable section
namespace AspisR1.FJo_FoldedSelected
open Aeneas Aeneas.Std Result AspisR1Stage2
open OraclePortCompactDraft OraclePortSelectedDraft OraclePortStoredDecisionDraftC4
open AspisV8R19.DuplexFrames
/-- Actual comparison selects SAME literal V, including repeated folded parents.
Recovery is consumed locally; the original At theorem derives its collision alternative. -/
theorem value {C : Type} (err : C) (seed : DrvC_Installation.Configuration FIo_Install.W C)
    (r : NP6_StdModel.Reservation) (early : Bool)
    (proof : Slice U8) (p : verifier.Prepared) (a out : verifier.Accumulator)
    (g : Array FIp_DotsAdapter.E 29#usize) (geo : verifier.QueryGeometry) (b bout : verifier.BatchedWeights)
    (o : Port4C_QueryValues.Observation
      (if early then Tx1Q_QueryBridge.leaves (FIp_Install.configuration err seed r).query else
        Port3_QueryStage.release (Port4C_RowStd.install (Port5Q1_QueryPorts.install
          (FIp_Install.configuration err seed r).query))) proof p a out g none geo b bout)
    (parsed : Parsed) (q : Fin 22 → Fin 262144) (tr : RawCutTranscriptRun.ErasedPrefix)
    (data : MatchingSupport.Data AspisWideTower.WideExact)
    (read : LiteralMatchingData.read (typedRows parsed q tr)=some data)
    (wire : parsed.wire=MultiproofConeCanonical.bytesOf proof.val) (size : proof.val.length=57607)
    (recovered : Nat → Option Bytes)
    (authenticated : ∀ pos,pos<22 → recovered (index q 2 pos)=some (OraclePortPackedChoiceC4.payload parsed 2 pos))
    (j : Fin 22) (position : a.next.val=j.val)
    (raw : (Port5Q1_GeometryBinding.queryAt p.queries a.next.val).val=(q j).val) :
    CheckpointBytes5Output.ofE o.selected=data.V (q j) := by
  cases early
  all_goals
    let c := FIp_Install.configuration err seed r
    have decoder : Port5Q1_OpeningValues.SessionAS3 (Port3_QueryStage.release c.query) :=
      ⟨(F3Y_InstalledLaws.primitives err (FIo_Install.select r seed) r).decoder.decode⟩
    have quartet := Port5Q1_ObservedOpening.quartet (Port3_QueryStage.release c.query) decoder
      proof p a out g none geo b bout parsed q tr data read wire size recovered authenticated j position o
    have qr : o.query.val=(q j).val := by
      rw [←FJo_QueryRaw.value p.queries a.next (by rw [position];exact j.isLt) o.query o.query_read]
      exact raw
    have compared : o.folded=o.selected := FIp_InstalledLaws.compared err seed r _ _ o.comparison
    have folded := Port5Q1_CircleObservation.selected (Tx1Q_QueryBridge.leaves c.query)
      ⟨fun x y comp=>congrArg CheckpointBytes5Output.ofE (FIp_InstalledLaws.compared err seed r x y comp)⟩
      proof p a out g none geo b bout o (q j) data.V qr quartet.2
    rw [compared] at folded
    exact folded
#print axioms value
end AspisR1.FJo_FoldedSelected
end
