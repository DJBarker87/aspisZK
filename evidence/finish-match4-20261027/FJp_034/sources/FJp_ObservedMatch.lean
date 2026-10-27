import FJp_Query00
import FJp_Query01
import FJp_Query02
import FJp_Query03
import FJp_Query04
import FJp_Query05
import FJp_Query06
import FJp_Query07
import FJp_Query08
import FJp_Query09
import FJp_Query10
import FJp_Query11
import FJp_Query12
import FJp_Query13
import FJp_Query14
import FJp_Query15
import FJp_Query16
import FJp_Query17
import FJp_Query18
import FJp_Query19
import FJp_Query20
import FJp_Query21
set_option autoImplicit false
noncomputable section
namespace AspisR1.FJp_ObservedMatch
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
    (alpha : CheckpointBytes5Output.ofE o.alpha0=data.alpha0)
    (ix : algebraMap Port5Q1_QueryPorts.FP E (S7JoinBasisMachine.decode (Port5Q1_GeometryBinding.lane o.inverse 0))=(exactCircleX (q j))⁻¹)
    (iy : algebraMap Port5Q1_QueryPorts.FP E (S7JoinBasisMachine.decode (Port5Q1_GeometryBinding.lane o.inverse 1))=(exactCircleY (q j))⁻¹)
    (recovered : Nat → Option Bytes)
    (authenticated : ∀ pos,pos<22 → recovered (OraclePortSelectedDraft.index q 2 pos)=some (OraclePortPackedChoiceC4.payload parsed 2 pos))
    (raw : (Port5Q1_GeometryBinding.queryAt p.queries a.next.val).val=(q j).val) :
    MatchingSupport.match0 data (q j) := by
  revert position ix iy raw
  induction j using Fin.induction with
  | zero =>
    intro position ix iy raw
    with_reducible exact (FJp_Query00.value err seed r early proof p a out g geo b bout o parsed q tr data read queries wire size position hg powers alpha ix iy recovered authenticated raw)
  | succ k ih =>
    fin_cases k
    · intro position ix iy raw
      with_reducible exact (FJp_Query01.value err seed r early proof p a out g geo b bout o parsed q tr data read queries wire size position hg powers alpha ix iy recovered authenticated raw)
    · intro position ix iy raw
      with_reducible exact (FJp_Query02.value err seed r early proof p a out g geo b bout o parsed q tr data read queries wire size position hg powers alpha ix iy recovered authenticated raw)
    · intro position ix iy raw
      with_reducible exact (FJp_Query03.value err seed r early proof p a out g geo b bout o parsed q tr data read queries wire size position hg powers alpha ix iy recovered authenticated raw)
    · intro position ix iy raw
      with_reducible exact (FJp_Query04.value err seed r early proof p a out g geo b bout o parsed q tr data read queries wire size position hg powers alpha ix iy recovered authenticated raw)
    · intro position ix iy raw
      with_reducible exact (FJp_Query05.value err seed r early proof p a out g geo b bout o parsed q tr data read queries wire size position hg powers alpha ix iy recovered authenticated raw)
    · intro position ix iy raw
      with_reducible exact (FJp_Query06.value err seed r early proof p a out g geo b bout o parsed q tr data read queries wire size position hg powers alpha ix iy recovered authenticated raw)
    · intro position ix iy raw
      with_reducible exact (FJp_Query07.value err seed r early proof p a out g geo b bout o parsed q tr data read queries wire size position hg powers alpha ix iy recovered authenticated raw)
    · intro position ix iy raw
      with_reducible exact (FJp_Query08.value err seed r early proof p a out g geo b bout o parsed q tr data read queries wire size position hg powers alpha ix iy recovered authenticated raw)
    · intro position ix iy raw
      with_reducible exact (FJp_Query09.value err seed r early proof p a out g geo b bout o parsed q tr data read queries wire size position hg powers alpha ix iy recovered authenticated raw)
    · intro position ix iy raw
      with_reducible exact (FJp_Query10.value err seed r early proof p a out g geo b bout o parsed q tr data read queries wire size position hg powers alpha ix iy recovered authenticated raw)
    · intro position ix iy raw
      with_reducible exact (FJp_Query11.value err seed r early proof p a out g geo b bout o parsed q tr data read queries wire size position hg powers alpha ix iy recovered authenticated raw)
    · intro position ix iy raw
      with_reducible exact (FJp_Query12.value err seed r early proof p a out g geo b bout o parsed q tr data read queries wire size position hg powers alpha ix iy recovered authenticated raw)
    · intro position ix iy raw
      with_reducible exact (FJp_Query13.value err seed r early proof p a out g geo b bout o parsed q tr data read queries wire size position hg powers alpha ix iy recovered authenticated raw)
    · intro position ix iy raw
      with_reducible exact (FJp_Query14.value err seed r early proof p a out g geo b bout o parsed q tr data read queries wire size position hg powers alpha ix iy recovered authenticated raw)
    · intro position ix iy raw
      with_reducible exact (FJp_Query15.value err seed r early proof p a out g geo b bout o parsed q tr data read queries wire size position hg powers alpha ix iy recovered authenticated raw)
    · intro position ix iy raw
      with_reducible exact (FJp_Query16.value err seed r early proof p a out g geo b bout o parsed q tr data read queries wire size position hg powers alpha ix iy recovered authenticated raw)
    · intro position ix iy raw
      with_reducible exact (FJp_Query17.value err seed r early proof p a out g geo b bout o parsed q tr data read queries wire size position hg powers alpha ix iy recovered authenticated raw)
    · intro position ix iy raw
      with_reducible exact (FJp_Query18.value err seed r early proof p a out g geo b bout o parsed q tr data read queries wire size position hg powers alpha ix iy recovered authenticated raw)
    · intro position ix iy raw
      with_reducible exact (FJp_Query19.value err seed r early proof p a out g geo b bout o parsed q tr data read queries wire size position hg powers alpha ix iy recovered authenticated raw)
    · intro position ix iy raw
      with_reducible exact (FJp_Query20.value err seed r early proof p a out g geo b bout o parsed q tr data read queries wire size position hg powers alpha ix iy recovered authenticated raw)
    · intro position ix iy raw
      with_reducible exact (FJp_Query21.value err seed r early proof p a out g geo b bout o parsed q tr data read queries wire size position hg powers alpha ix iy recovered authenticated raw)
#print axioms value
end AspisR1.FJp_ObservedMatch
end
