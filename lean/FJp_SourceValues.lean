import FJo_QueryBatched
import FJo_ObservedCircle
import FJo_FoldedSelected
import FJp_MatchingJoin
set_option autoImplicit false
noncomputable section
namespace AspisR1.FJp_SourceValues
open Aeneas Aeneas.Std Result AspisR1Stage2
open OraclePortCompactDraft OraclePortStoredDecisionDraftC4
open AspisV8R19.DuplexFrames
open AspisWide.FinalEncoder
abbrev E := AspisWideTower.WideExact
attribute [local irreducible] TwoFoldExtraction.batchedWord FirstFold.fibre FirstFold.foldWord
/-- Complete local source query matching. Powers/alpha/geometry/recovery operands
must be supplied by their checked SAME-run producers; this is no new owner field. -/
theorem value {C : Type} (err : C) (seed : DrvC_Installation.Configuration FIo_Install.W C)
    (r : NP6_StdModel.Reservation) (early : Bool)
    (proof : Slice U8) (p : verifier.Prepared) (a out : verifier.Accumulator)
    (g : Array FIp_DotsAdapter.E 29#usize) (geo : verifier.QueryGeometry) (b bout : verifier.BatchedWeights)
    (o : Port4C_QueryValues.Observation
      (if early then Tx1Q_QueryBridge.leaves (FIp_Install.configuration err seed r).query else
        Port3_QueryStage.release (Port4C_RowStd.install (Port5Q1_QueryPorts.install
          (FIp_Install.configuration err seed r).query))) proof p a out g none geo b bout)
    (parsed : Parsed) (q : Fin 22 → Fin 262144) (tr : RawCutTranscriptRun.ErasedPrefix)
    (data : MatchingSupport.Data E) (read : LiteralMatchingData.read (typedRows parsed q tr)=some data)
    (queries : OraclePortSelectedDraft.queries tr=some q)
    (wire : parsed.wire=MultiproofConeCanonical.bytesOf proof.val) (size : proof.val.length=57607)
    (j : Fin 22) (position : a.next.val=j.val)
    (hg : FIo_ArrayCanon.Holds (FIp_DotsAdapter.toArray g))
    (powers : ∀ l : Fin 29,FIp_ArrayValue.value (FIp_DotsAdapter.toArray g) l.val=data.gamma^l.val)
    (recovered : Nat → Option Bytes)
    (authenticated : ∀ pos,pos<22 → recovered (OraclePortSelectedDraft.index q 2 pos)=some (OraclePortPackedChoiceC4.payload parsed 2 pos))
    (raw : (Port5Q1_GeometryBinding.queryAt p.queries a.next.val).val=(q j).val) :
    Port5Q1_OpeningValues.values o.dots=FirstFold.fibre (TwoFoldExtraction.batchedWord data.W data.gamma) (q j) ∧
    CheckpointBytes5Output.ofE o.selected=data.V (q j) ∧
    CheckpointBytes5Output.ofE o.selected=FoldRuntimeAlgebra.circleWithInverses
      (CheckpointBytes5Output.ofE o.alpha0)
      (algebraMap Port5Q1_QueryPorts.FP E (S7JoinBasisMachine.decode (Port5Q1_GeometryBinding.lane o.inverse 0)))
      (algebraMap Port5Q1_QueryPorts.FP E (S7JoinBasisMachine.decode (Port5Q1_GeometryBinding.lane o.inverse 1)))
      (Port5Q1_OpeningValues.values o.dots) := by
  refine ⟨?_,?_,?_⟩
  · exact FJo_QueryBatched.value _ proof p a out g geo b bout o
      (by cases early <;> rfl) (by cases early <;> rfl) size parsed wire q tr data read queries j position hg powers
  · exact FJo_FoldedSelected.value err seed r early proof p a out g geo b bout o
      parsed q tr data read wire size recovered authenticated j position raw
  · exact FJo_ObservedCircle.value err seed r early proof p a out g geo b bout o
#print axioms value
end AspisR1.FJp_SourceValues
end
