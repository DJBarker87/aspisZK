import RPz8_Rc10_Top
import NDO_JFs_TX2_Dots
import NDO_JFr_TX2_CircleAfterDots
import NDO_JFr_TX2_Partial
import NDO_JFn_HashModelNonvacuity
set_option autoImplicit false
noncomputable section
namespace AspisR1.JFs_TX2_Partial
open Aeneas Aeneas.Std Result
open AspisV8R19.DuplexFrames AspisV8R19.SourceDuplexStep

def Calls (seed : Port3_NativeQueryBody.Ops) : Prop := ∀ i : Fin 12,
  (JFr_TX2_DotsBinding.ops seed).op20 (JFo_Opening.value (JFn_Values.position i))
    JFr_TX2_Powers.value=ok (JFs_TX2_Dots.value i) ∧
  ∀ inverse : Array U32 5#usize, ∃ out,
    (JFr_TX2_DotsBinding.ops seed).op17 JFq_Alpha0.scalar (JFs_TX2_Dots.value i) inverse=ok out ∧
    Port4C_QueryArithmetic.CanonE out

theorem calls (seed : Port3_NativeQueryBody.Ops) : Calls seed := by
  intro i
  refine ⟨JFs_TX2_Dots.source seed i,?_⟩
  intro inverse
  exact JFr_TX2_CircleAfterDots.source seed (JFn_Values.position i) JFr_TX2_Powers.value
    (JFs_TX2_Dots.value i) inverse (JFs_TX2_Dots.source seed i)

/-- Same saved-checkpoint transport with complete actual dot calls. Geometry,
circle equality, chained query success, Merkle and finish remain open. -/
theorem on_saved (saved : alloc.vec.Vec U8) (same : saved.val=JFx_NativeBytes.checkpoint.val)
    {Hash : Type} (H : Bytes → State) (D : VTop_Stages.aspis_core.digest.Digest32 Hash) (hash : Hash)
    (realizes : JFn_HashBoundary.Realizes H) (seed : Port3_NativeQueryBody.Ops) :
    Port4A_ReaderInstall.reader true (JFn_HashBoundary.dictionary H D)
      (⟨saved.val,saved.property⟩ : Slice U8) JFx_NativeBytes.proof JFx_NativeBytes.publicInput .S2 hash=
      ok (.Ok (JFo_Prepared.value,JFo_Prepared.accumulator)) ∧
    Tx2N_Powers.powers 29#usize JFo_Prepared.value.gamma=ok JFr_TX2_Powers.value ∧
    Port3_NativePendingInstall.source true JFo_Prepared.accumulator.weights.deref=ok (.Ok JFo_Pending.value) ∧
    (∀ i : Fin 12,
      (JFr_TX2_DotsBinding.ops seed).op0 4#usize
        (Port3_NativeQueryBody.verifier.candidate.query_values.closure.Insts.CoreOpsFunctionFnMutTupleUsizeWideExact
          (JFr_TX2_DotsBinding.ops seed)) (JFo_Opening.value (JFn_Values.position i))=ok (JFn_Values.value i)) ∧
    Calls seed := by
  obtain ⟨reader,powers,pending,arrays,_⟩ := JFr_TX2_Partial.on_saved saved same H D hash realizes seed
  exact ⟨reader,powers,pending,arrays,calls seed⟩

/-- Local model-oracle non-vacuity; this is not SHA256 realization, acceptance
of either transaction, or satisfiability of the deployed top. -/
theorem inhabited {Hash : Type} (D : VTop_Stages.aspis_core.digest.Digest32 Hash) (hash : Hash)
    (background : Bytes → State) (seed : Port3_NativeQueryBody.Ops) :
    ∃ H : Bytes → State, JFn_HashBoundary.Realizes H ∧
      Port4A_ReaderInstall.reader true (JFn_HashBoundary.dictionary H D)
        JFx_NativeBytes.checkpoint JFx_NativeBytes.proof JFx_NativeBytes.publicInput .S2 hash=
        ok (.Ok (JFo_Prepared.value,JFo_Prepared.accumulator)) ∧ Calls seed := by
  exact ⟨JFn_HashModelNonvacuity.extension background,JFn_HashModelNonvacuity.realizes background,
    JFn_HashModelNonvacuity.reader D hash background,calls seed⟩

#print axioms AspisR1.Rc10_Top.deployed
#print axioms calls
#print axioms on_saved
#print axioms inhabited
#print on_saved
end AspisR1.JFs_TX2_Partial
end
