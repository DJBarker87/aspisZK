import Port4C_SumField

set_option autoImplicit false
noncomputable section
namespace AspisR1.Port4C_FlushField
open Aeneas Aeneas.Std Result
open S7Kani3CallerTrace (PushTrace Sum)
open Port3_FlushInstall (K BW)
open Port4C_SumField (weight)

theorem model_field (row : S8OwnedP6ValueModel.Row) :
    CheckpointBytes5Output.ofK
      (Port3_FlushInstall.fromMutable (S8Kani2FinishReferenceJoin.toFinish (S8OwnedP6Finish.modelValue row)))=
        S8JoinFinishField.rawValue row := by
  rw [Port4C_SumField.source_words]
  exact S8JoinFinishField.modelValue_field row

/-- Decode ALL64 weights from the SAME actual retained flush return. Raw
congruence comes from the native query's derived PushTrace, not a new finish
congruence or independently successful output premise. -/
theorem accepted (old : S8OwnedP6Finish.Weights) (b : BW) (sum : Sum)
    (input out : Slice K) (size : input.val.length=64) (rawSize : b.raw.val.length=64)
    (trace : PushTrace old (Port3_RowsInstall.toBW b) sum)
    (h : Port3_FlushInstall.flush b input=ok out) :
    out.val.length=64 ∧ ∀ i : Fin 64,
      CheckpointBytes5Output.ofK ((out.val[i.val]?).getD
        (CheckpointBytes4SavedFields.sourceK 0))=weight sum i.val := by
  have contents := Port3_FlushInstall.accepted_contents b input out (by omega) h
  refine ⟨contents.2.trans size,?_⟩
  intro i
  have hi : i.val<b.raw.val.length := by omega
  let row := b.raw.val[i.val]
  have rawRead : b.raw.val[i.val]?=some row := List.getElem?_eq_getElem hi
  have outputRead : out.val[i.val]?=some
      (Port3_FlushInstall.fromMutable (S8Kani2FinishReferenceJoin.toFinish (S8OwnedP6Finish.modelValue row))) := by
    rw [contents.1,List.getElem?_map,List.getElem?_take]
    simp only [size,i.isLt,if_pos,rawRead,Option.map_some]
  rw [outputRead,Option.getD_some,model_field]
  exact Port4C_SumField.raw_weight old (Port3_RowsInstall.toBW b) sum trace i.val row rawRead

#print axioms model_field
#print axioms accepted
end AspisR1.Port4C_FlushField
end
