import NDO_JHl_SumField
set_option autoImplicit false
noncomputable section
namespace AspisR1.JHl_FlushSum
open Aeneas Aeneas.Std Result AspisR1Stage2
open S7Kani3CallerTrace (Sum PushTrace)
open JHl_SumField (value)

theorem source (old : Slice aspis_core.field.QM31) (b : verifier.BatchedWeights)
    (out : Slice aspis_core.field.QM31) (sum : Sum)
    (size : old.val.length=64) (length : b.raw.val.length=64)
    (history : PushTrace (Port3_PendingInstall.owned old) (Port3_RowsInstall.toBW b) sum)
    (flush : Port3_FlushInstall.flush b old=ok out) (j : Fin 64) :
    ∃ q,out.val[j.val]?=some q ∧ CheckpointBytes5Output.ofK q=value sum j.val ∧
      Port3_FlushInstall.Canonical q := by
  obtain ⟨actual,run,cells⟩ := S7Kani3CallerTrace.reached_finish _ _ _ history
  have sameRun : Port3_FlushInstall.flush b old=ok (Port3_FlushInstall.fromSlice actual) := by
    change S8Kani2MutableExtraction.batched_weights.BatchedWeights.finish
      (⟨b.raw,b.terms⟩ : S8Kani2MutableValue.F.BW)
      (S8Kani2FinishReferenceJoin.toSlice (Port3_FlushInstall.toWeights old))=ok actual at run
    unfold Port3_FlushInstall.flush
    rw [run,bind_tc_ok]
  have eq : out=Port3_FlushInstall.fromSlice actual := Result.ok.inj (flush.symm.trans sameRun)
  let idx : Usize := Usize.ofNat j.val (by have := j.isLt;scalar_tac)
  obtain ⟨q,read,words⟩ := cells idx (by simp only [Port3_PendingInstall.owned,Port3_FlushInstall.toWeights,alloc.vec.Vec.length,List.length_map,size];change j.val<64;exact j.isLt)
  have readValue : actual.val[j.val]?=some q := by
    unfold Slice.index_usize at read
    split at read
    · cases read
    · rename_i x hx
      exact hx.trans (congrArg some (Result.ok.inj read))
  refine ⟨Port3_FlushInstall.fromMutable q,?_,?_,?_⟩
  · rw [eq]
    simp only [Port3_FlushInstall.fromSlice,List.getElem?_map,readValue,Option.map_some]
  · have h0 := (words 0).1
    have h1 := (words 1).1
    have h2 := (words 2).1
    have h3 := (words 3).1
    change q.c0.a.val=sum j.val 0%2147483647 at h0
    change q.c0.b.val=sum j.val 1%2147483647 at h1
    change q.c1.a.val=sum j.val 2%2147483647 at h2
    change q.c1.b.val=sum j.val 3%2147483647 at h3
    change (⟨⟨(q.c0.a.val : AspisV8R15.ExactTowerBase.M31Exact),q.c0.b.val⟩,
      ⟨q.c1.a.val,q.c1.b.val⟩⟩ : JHl_SumField.K)=value sum j.val
    rw [h0,h1,h2,h3]
    ext <;> simp [value,AspisV8R15.ExactTowerBase.M31Exact,AspisV8R15.ExactTowerBase.P,ZMod.natCast_mod]
  · exact ⟨(words 0).2,(words 1).2,(words 2).2,(words 3).2⟩
#print axioms source
end AspisR1.JHl_FlushSum
end
