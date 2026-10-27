import RPt_FJp_QueryLaw
import RPt_FJp_Fin22
import RPt_FJp_Query00
import RPt_FJp_Query01
import RPt_FJp_Query02
import RPt_FJp_Query03
import RPt_FJp_Query04
import RPt_FJp_Query05
import RPt_FJp_Query06
import RPt_FJp_Query07
import RPt_FJp_Query08
import RPt_FJp_Query09
import RPt_FJp_Query10
import RPt_FJp_Query11
import RPt_FJp_Query12
import RPt_FJp_Query13
import RPt_FJp_Query14
import RPt_FJp_Query15
import RPt_FJp_Query16
import RPt_FJp_Query17
import RPt_FJp_Query18
import RPt_FJp_Query19
import RPt_FJp_Query20
import RPt_FJp_Query21
set_option autoImplicit false
noncomputable section
namespace AspisR1.FJp_ObservedMatch
open Aeneas Aeneas.Std Result AspisR1Stage2
open OraclePortCompactDraft OraclePortStoredDecisionDraftC4
open AspisV8R19.DuplexFrames
open AspisWide.FinalEncoder
abbrev E := AspisWideTower.WideExact
attribute [local irreducible] TwoFoldExtraction.batchedWord FirstFold.fibre FirstFold.foldWord exactCircleX exactCircleY
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
  let P := FJp_QueryLaw.Step data q a.next.val
    (Port5Q1_GeometryBinding.queryAt p.queries a.next.val).val
    (algebraMap Port5Q1_QueryPorts.FP E (S7JoinBasisMachine.decode (Port5Q1_GeometryBinding.lane o.inverse 0)))
    (algebraMap Port5Q1_QueryPorts.FP E (S7JoinBasisMachine.decode (Port5Q1_GeometryBinding.lane o.inverse 1)))
  have h0 : P 0 := by
    intro pos hx hy hraw
    with_reducible exact (FJp_Query00.value err seed r early proof p a out g geo b bout o parsed q tr data read queries wire size pos hg powers alpha hx hy recovered authenticated hraw)
  have h1 : P 1 := by
    intro pos hx hy hraw
    with_reducible exact (FJp_Query01.value err seed r early proof p a out g geo b bout o parsed q tr data read queries wire size pos hg powers alpha hx hy recovered authenticated hraw)
  have h2 : P 2 := by
    intro pos hx hy hraw
    with_reducible exact (FJp_Query02.value err seed r early proof p a out g geo b bout o parsed q tr data read queries wire size pos hg powers alpha hx hy recovered authenticated hraw)
  have h3 : P 3 := by
    intro pos hx hy hraw
    with_reducible exact (FJp_Query03.value err seed r early proof p a out g geo b bout o parsed q tr data read queries wire size pos hg powers alpha hx hy recovered authenticated hraw)
  have h4 : P 4 := by
    intro pos hx hy hraw
    with_reducible exact (FJp_Query04.value err seed r early proof p a out g geo b bout o parsed q tr data read queries wire size pos hg powers alpha hx hy recovered authenticated hraw)
  have h5 : P 5 := by
    intro pos hx hy hraw
    with_reducible exact (FJp_Query05.value err seed r early proof p a out g geo b bout o parsed q tr data read queries wire size pos hg powers alpha hx hy recovered authenticated hraw)
  have h6 : P 6 := by
    intro pos hx hy hraw
    with_reducible exact (FJp_Query06.value err seed r early proof p a out g geo b bout o parsed q tr data read queries wire size pos hg powers alpha hx hy recovered authenticated hraw)
  have h7 : P 7 := by
    intro pos hx hy hraw
    with_reducible exact (FJp_Query07.value err seed r early proof p a out g geo b bout o parsed q tr data read queries wire size pos hg powers alpha hx hy recovered authenticated hraw)
  have h8 : P 8 := by
    intro pos hx hy hraw
    with_reducible exact (FJp_Query08.value err seed r early proof p a out g geo b bout o parsed q tr data read queries wire size pos hg powers alpha hx hy recovered authenticated hraw)
  have h9 : P 9 := by
    intro pos hx hy hraw
    with_reducible exact (FJp_Query09.value err seed r early proof p a out g geo b bout o parsed q tr data read queries wire size pos hg powers alpha hx hy recovered authenticated hraw)
  have h10 : P 10 := by
    intro pos hx hy hraw
    with_reducible exact (FJp_Query10.value err seed r early proof p a out g geo b bout o parsed q tr data read queries wire size pos hg powers alpha hx hy recovered authenticated hraw)
  have h11 : P 11 := by
    intro pos hx hy hraw
    with_reducible exact (FJp_Query11.value err seed r early proof p a out g geo b bout o parsed q tr data read queries wire size pos hg powers alpha hx hy recovered authenticated hraw)
  have h12 : P 12 := by
    intro pos hx hy hraw
    with_reducible exact (FJp_Query12.value err seed r early proof p a out g geo b bout o parsed q tr data read queries wire size pos hg powers alpha hx hy recovered authenticated hraw)
  have h13 : P 13 := by
    intro pos hx hy hraw
    with_reducible exact (FJp_Query13.value err seed r early proof p a out g geo b bout o parsed q tr data read queries wire size pos hg powers alpha hx hy recovered authenticated hraw)
  have h14 : P 14 := by
    intro pos hx hy hraw
    with_reducible exact (FJp_Query14.value err seed r early proof p a out g geo b bout o parsed q tr data read queries wire size pos hg powers alpha hx hy recovered authenticated hraw)
  have h15 : P 15 := by
    intro pos hx hy hraw
    with_reducible exact (FJp_Query15.value err seed r early proof p a out g geo b bout o parsed q tr data read queries wire size pos hg powers alpha hx hy recovered authenticated hraw)
  have h16 : P 16 := by
    intro pos hx hy hraw
    with_reducible exact (FJp_Query16.value err seed r early proof p a out g geo b bout o parsed q tr data read queries wire size pos hg powers alpha hx hy recovered authenticated hraw)
  have h17 : P 17 := by
    intro pos hx hy hraw
    with_reducible exact (FJp_Query17.value err seed r early proof p a out g geo b bout o parsed q tr data read queries wire size pos hg powers alpha hx hy recovered authenticated hraw)
  have h18 : P 18 := by
    intro pos hx hy hraw
    with_reducible exact (FJp_Query18.value err seed r early proof p a out g geo b bout o parsed q tr data read queries wire size pos hg powers alpha hx hy recovered authenticated hraw)
  have h19 : P 19 := by
    intro pos hx hy hraw
    with_reducible exact (FJp_Query19.value err seed r early proof p a out g geo b bout o parsed q tr data read queries wire size pos hg powers alpha hx hy recovered authenticated hraw)
  have h20 : P 20 := by
    intro pos hx hy hraw
    with_reducible exact (FJp_Query20.value err seed r early proof p a out g geo b bout o parsed q tr data read queries wire size pos hg powers alpha hx hy recovered authenticated hraw)
  have h21 : P 21 := by
    intro pos hx hy hraw
    with_reducible exact (FJp_Query21.value err seed r early proof p a out g geo b bout o parsed q tr data read queries wire size pos hg powers alpha hx hy recovered authenticated hraw)
  have joined := FJp_Fin22.all P h0 h1 h2 h3 h4 h5 h6 h7 h8 h9 h10 h11 h12 h13 h14 h15 h16 h17 h18 h19 h20 h21 j
  dsimp only [P,FJp_QueryLaw.Step] at joined
  with_reducible exact (joined position ix iy raw)
#print axioms value
end AspisR1.FJp_ObservedMatch
end
