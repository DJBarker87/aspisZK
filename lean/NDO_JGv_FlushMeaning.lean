import NDO_JGv_QueryRows
import NDO_JGc_TX2_InstalledQuery
set_option autoImplicit false
noncomputable section
namespace AspisR1.JGv_FlushMeaning
open Aeneas Aeneas.Std Result AspisR1Stage2
abbrev K := SAQ_WideABI.K
def limb (q : K) (k : Fin 4) : U32 :=
  S7Kani2OwnedRowRefinement.powerLimb (Port3_RowsInstall.toK q) k

theorem transport (q : S8Kani2MutableValue.F.Q) (k : Fin 4) :
    limb (Port3_FlushInstall.fromMutable q) k=S8Kani2CallerJoin.coordinate q k := by
  fin_cases k <;> rfl
#print axioms transport

theorem source {C : Type} (err : C) (geometry : Port3_NativeGeometryBody.Ops C)
    (seed : Port3_NativeQueryBody.Ops) (a : verifier.Accumulator)
    (b : verifier.BatchedWeights) (flushed : Slice K)
    (updates : JFz_TX2_AccumulationChain.updates seed 12=ok (a,b))
    (flush : Port3_FlushInstall.flush b a.weights.deref=ok flushed) :
    ∀ i : Usize,i.val<64 → ∃ q,Slice.index_usize flushed i=ok q ∧
      ∀ k : Fin 4,((limb q k).val : JGv_QueryRows.F)=JGv_QueryRows.weights 12 i.val k := by
  obtain ⟨hw,_,_,_,_,_,sum,trace,phase,meaning⟩ := JGv_QueryRows.source err geometry seed 12 (by omega) a b updates
  obtain ⟨out,run,cells⟩ := S7Kani3CallerTrace.reached_finish JFn_PendingHistory.old
    (Port3_RowsInstall.toBW b) sum trace
  have mapped : Port3_FlushInstall.flush b JFo_Prepared.accumulator.weights.deref=
      ok (Port3_FlushInstall.fromSlice out) := by
    unfold Port3_FlushInstall.flush
    rw [show S8Kani2MutableExtraction.batched_weights.BatchedWeights.finish
      (⟨b.raw,b.terms⟩ : S8Kani2MutableValue.F.BW)
      (S8Kani2FinishReferenceJoin.toSlice (Port3_FlushInstall.toWeights JFo_Prepared.accumulator.weights.deref))=ok out from run,
      bind_tc_ok]
  rw [hw,mapped] at flush
  have same := Result.ok.inj flush
  subst flushed
  intro i hi
  obtain ⟨q,read,coordinates⟩ := cells i (by change i.val<JFo_Prepared.accumulator.weights.val.length;rw [JFo_Prepared.weights_length];exact hi)
  refine ⟨Port3_FlushInstall.fromMutable q,?_,?_⟩
  · simp only [Slice.index_usize,Slice.getElem?_Usize_eq] at read ⊢
    simp only [Port3_FlushInstall.fromSlice,List.getElem?_map]
    cases h : out.val[i.val]? with
    | none => simp only [h] at read;cases read
    | some actual =>
      simp only [h] at read
      have eq := Result.ok.inj read
      simp only [h,eq,Option.map_some]
  · intro k
    rw [transport,(coordinates k).1,ZMod.natCast_mod]
    exact meaning i.val hi k
#print axioms source
end AspisR1.JGv_FlushMeaning
end
