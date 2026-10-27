import RPt_FJo_QueryBatched
import RPt_FJo_ObservedCircle
import RPt_FJo_FoldedSelected
import RPt_FJp_LiteralJoin
import RPt_FJp_SourceValues
set_option autoImplicit false
noncomputable section
namespace AspisR1.FJp_Query08
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
    (position : a.next.val=(8 : Fin 22).val)
    (hg : FIo_ArrayCanon.Holds (FIp_DotsAdapter.toArray g))
    (powers : ∀ l : Fin 29,FIp_ArrayValue.value (FIp_DotsAdapter.toArray g) l.val=data.gamma^l.val)
    (alpha : CheckpointBytes5Output.ofE o.alpha0=data.alpha0)
    (ix : algebraMap Port5Q1_QueryPorts.FP E (S7JoinBasisMachine.decode (Port5Q1_GeometryBinding.lane o.inverse 0))=(exactCircleX (q (8 : Fin 22)))⁻¹)
    (iy : algebraMap Port5Q1_QueryPorts.FP E (S7JoinBasisMachine.decode (Port5Q1_GeometryBinding.lane o.inverse 1))=(exactCircleY (q (8 : Fin 22)))⁻¹)
    (recovered : Nat → Option Bytes)
    (authenticated : ∀ pos,pos<22 → recovered (OraclePortSelectedDraft.index q 2 pos)=some (OraclePortPackedChoiceC4.payload parsed 2 pos))
    (raw : (Port5Q1_GeometryBinding.queryAt p.queries a.next.val).val=(q (8 : Fin 22)).val) :
    MatchingSupport.match0 data (q (8 : Fin 22)) := by
  obtain ⟨dots,selected,circle⟩ := FJp_SourceValues.value err seed r early proof p a out g geo b bout o
    parsed q tr data read queries wire size 8 position hg powers recovered authenticated raw
  with_reducible exact (FJp_LiteralJoin.value data (q 8)
    (CheckpointBytes5Output.ofE o.alpha0)
    (algebraMap Port5Q1_QueryPorts.FP E (S7JoinBasisMachine.decode (Port5Q1_GeometryBinding.lane o.inverse 0)))
    (algebraMap Port5Q1_QueryPorts.FP E (S7JoinBasisMachine.decode (Port5Q1_GeometryBinding.lane o.inverse 1)))
    (CheckpointBytes5Output.ofE o.selected) (Port5Q1_OpeningValues.values o.dots)
    alpha ix iy dots circle selected)
#print axioms value
end AspisR1.FJp_Query08
end
