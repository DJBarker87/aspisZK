import SAF_Returns
import SAP_FinishSaved
import T2R_Finish
import AuS1_Finish
import Cons_Finish
import T2R_Reader
set_option autoImplicit false
noncomputable section
namespace AspisR1.SAF_FinishSaved
open Aeneas Aeneas.Std Result AspisR1Stage2 AspisR1Stage2.Stage2Finish
open scoped BigOperators
open AspisV8R19.DuplexFrames AspisV8R19.SourceDuplexStep
open MultiproofConeCanonical OraclePortCompactDraft OraclePortSelectedDraft OraclePortBatchDraft
open OraclePortStoredDecisionDraftC4 OraclePortCheckpointResumeC5
open RecordedBinaryExperimentBin (SourceInputs)
open RowFinish_Control
attribute [local instance] Classical.propDecidable
open AuS1_Finish
def Outcome {W : Type} (finish : FinishOps W)
    (v : verifier.View) (p : verifier.Prepared) (a : verifier.Accumulator)
    (proof : Slice U8) (savedVec : alloc.vec.Vec U8)
    (H : Bytes → State) (stored publicBytes : Bytes)
    (tx1p : AspisR1CurrentCaller.verifier.Prepared) (parsed : Parsed)
    (trace : List (Bytes × State))
    (semantic : List Bytes) (q : Fin 22 → Fin 262144)
    (tr : RawCutTranscriptRun.ErasedPrefix) (i : SourceInputs) (c : Context) : Prop :=
    p.variant = .S2 ∧ ∃ (alpha0 alpha1 : E) (alphas : Slice E),
    Array.index_usize p.alpha 0#usize = ok alpha0 ∧
    Array.index_usize p.alpha 1#usize = ok alpha1 ∧
    core.array.Array.index (core.ops.index.IndexSlice
      (core.slice.index.SliceIndexRangeToUsizeSlice E)) p.alpha { «end» := 2#usize } = ok alphas ∧
    ∃     (r0 : RoundValues finish v.round0 alpha0 p.claim)
    (r1 : RoundValues finish v.round1 alpha1 r0.value)
    (weights : W) (pair dot : E)
,
    finish.newWeights p.variant p.semantic_alpha p.z = ok (.Ok weights) ∧
    finish.pair weights alphas v.final_message p.kappa = ok (.Ok pair) ∧
    finish.dot v.final_message a.weights.deref = ok (.Ok dot) ∧
    r0.lhs = r0.rhs ∧ r1.lhs = r1.rhs ∧ pair = r1.value ∧ dot = a.rhs ∧
    ∀ (pairing_S3_S5_S9 : Port4D_Pairing.PairingLaws (Port3_FinishStage.release finish)
      CheckpointBytes5Output.ofE v p i.data)
    (matches_S4_S7 : ∀ j, MatchingSupport.match0 i.data (q j))
    (semantic_S3_S9 : R3SemanticRemainingJoins.EquationEndpoint i.decoded
      (typedRows (⟨bytesOf proof.val,semantic⟩ : Parsed) q tr) i.data)
    (dot_S5 : CheckpointBytes5Output.ofE dot = ∑ l : Fin 64, i.data.f l *
      LiteralOpeningView.eK ((CheckpointBytes5Output.accumulator a).weights l))
    (canonical_S3_S4_S5_S9 : ∀ x ∈ [r0.lhs,r0.rhs,r1.lhs,r1.rhs,pair,r1.value,dot,a.rhs],
      CheckpointBytes4ReaderFields.sourceE (CheckpointBytes5Output.ofE x) = x),
    Collision H trace parsed q ∨
    (decide (Port3_NativeFinishBody.verifier.finish_relation (Port4D_Round.native finish) v p a none =
      ok (.Ok ())) = OraclePortFrozen2.finish (⟨bytesOf proof.val,semantic⟩ : Parsed) q tr i (CheckpointBytes5Output.accumulator a) ∧
    decide (Port4D_FinishInstall.finish finish v p a none = ok (.Ok ())) =
      D0TypedChecks.verify (typedRows (⟨bytesOf proof.val,semantic⟩ : Parsed) q tr) i ∧
    D0TypedChecks.verify (typedRows ⟨bytesOf proof.val,semantic⟩ q tr) i = true)

theorem strengthen {W : Type} (finish : FinishOps W)
    (v : verifier.View) (p : verifier.Prepared) (a : verifier.Accumulator)
    (proof : Slice U8) (savedVec : alloc.vec.Vec U8)
    (H : Bytes → State) (stored publicBytes : Bytes)
    (tx1p : AspisR1CurrentCaller.verifier.Prepared) (parsed : Parsed)
    (trace : List (Bytes × State)) (semantic : List Bytes) (q : Fin 22 → Fin 262144)
    (tr : RawCutTranscriptRun.ErasedPrefix) (i : SourceInputs) (c : Context)
    (old : SAP_FinishSaved.Outcome finish v p a proof savedVec H stored publicBytes tx1p parsed trace semantic q tr i c)
    (success : Port4D_FinishInstall.finish finish v p a none = ok (.Ok ())) :
    Outcome finish v p a proof savedVec H stored publicBytes tx1p parsed trace semantic q tr i c := by
  obtain ⟨s2,alpha0,alpha1,alphas,ha0,ha1,has,rest⟩ := old
  obtain ⟨x0,x1,r0,r1,weights,xs,pair,dot,hx0,hx1,hw,hxs,hp,hd,e0,e1,ep,ed⟩ :=
    SAF_Returns.finish finish v p a s2 success
  have a0 : x0 = alpha0 := Result.ok.inj (hx0.symm.trans ha0)
  have a1 : x1 = alpha1 := Result.ok.inj (hx1.symm.trans ha1)
  have ass : xs = alphas := Result.ok.inj (hxs.symm.trans has)
  subst x0; subst x1; subst xs
  exact ⟨s2,alpha0,alpha1,alphas,ha0,ha1,has,r0,r1,weights,pair,dot,
    hw,hp,hd,e0,e1,ep,ed,rest r0 r1 weights pair dot hw hp hd⟩

#print axioms strengthen
end AspisR1.SAF_FinishSaved
end
