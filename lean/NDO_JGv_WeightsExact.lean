import NDO_JGv_WeightTable
import NDO_JGv_LimbEquality
set_option autoImplicit false
noncomputable section
namespace AspisR1.JGv_WeightsExact
open Aeneas Aeneas.Std Result AspisR1Stage2

theorem source {C : Type} (err : C) (geometry : Port3_NativeGeometryBody.Ops C)
    (seed : Port3_NativeQueryBody.Ops) (a : verifier.Accumulator)
    (b : verifier.BatchedWeights) (flushed : Slice SAQ_WideABI.K)
    (updates : JFz_TX2_AccumulationChain.updates seed 12=ok (a,b))
    (flush : Port3_FlushInstall.flush b a.weights.deref=ok flushed)
    (size : flushed.val.length=64) (canonical : ∀ q∈flushed.val,Port3_FlushInstall.Canonical q) :
    flushed=JGv_WeightsData.value := by
  apply Subtype.ext
  apply List.ext_getElem
  · exact size.trans JGv_WeightsData.length.symm
  · intro j hj hr
    have hi : j<64 := by omega
    let indexWord : Usize := Usize.ofNat j (by scalar_tac)
    obtain ⟨q,read,meaning⟩ := JGv_FlushMeaning.source err geometry seed a b flushed updates flush indexWord (by simpa [indexWord] using hi)
    have index : indexWord.val=j := by scalar_tac
    have read' : flushed.val[j]?=some q := by
      simp only [Slice.index_usize,Slice.getElem?_Usize_eq,index] at read
      cases h : flushed.val[j]? with
      | none => simp only [h] at read;cases read
      | some actual =>
        simp only [h] at read
        have same := Result.ok.inj read
        exact congrArg some same
    have get : q=flushed.val[j] := by simpa only [List.getElem?_eq_getElem hj,Option.some.injEq] using read'.symm
    have same := JGv_LimbEquality.source q (JGv_WeightsData.cell ⟨j,hi⟩)
      (canonical q (by rw [get];exact List.getElem_mem _)) (JGv_WeightsData.canonical ⟨j,hi⟩) (by
        intro k
        rw [meaning k,index]
        exact JGv_WeightTable.source ⟨j,hi⟩ k)
    exact get.symm.trans same
#print axioms source
end AspisR1.JGv_WeightsExact
end
