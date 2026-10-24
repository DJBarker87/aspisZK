import Port4D_FlushResult
set_option autoImplicit false
noncomputable section
namespace AspisR1.Port4D_FlushRows
open Aeneas Aeneas.Std Result AspisR1Stage2
open Port4D_FlushABI

def flush := Port3_NativeFlushBody.verifier.BatchedWeights.finish std value

/-- Pointwise S5 value-child agreement is needed only at reached row indices;
no whole-operation equality or raw bound is a hypothesis. -/
theorem lower_value (nativeValue : verifier.BatchedWeights → Usize → Result K)
    (b : verifier.BatchedWeights) (old : Slice K)
    (lengths : old.val.length ≤ b.raw.val.length)
    (S5_value : ∀ i : Usize, i.val < old.val.length → nativeValue b i = value b i) :
    Port3_NativeFlushBody.verifier.BatchedWeights.finish std nativeValue b old =
      Port3_FlushInstall.flush b old := by
  let f := fun j => Port3_FlushInstall.fromMutable (S8Kani2MutableValue.valueAt ⟨b.raw,b.terms⟩ j)
  have values : ∀ i : Usize, i.val < old.val.length → value b i = ok (f i.val) := by
    intro i hi
    unfold value
    rw [S8Kani2MutableValue.valueAt_success ⟨b.raw,b.terms⟩ i (by change i.val < b.raw.val.length; omega)]
    rfl
  rw [finish_total b nativeValue old f (by intro i hi; exact (S5_value i hi).trans (values i hi))]
  rw [← reference_eq b old lengths,finish_total b value old f values]

theorem accepted_rows (b : verifier.BatchedWeights) (old out : Slice K)
    (lengths : old.val.length ≤ b.raw.val.length) (success : flush b old = ok out) :
    out.val = (b.raw.val.take old.val.length).map (fun row =>
      Port3_FlushInstall.fromMutable (S8Kani2FinishReferenceJoin.toFinish (S8OwnedP6Finish.modelValue row))) ∧
    out.val.length = old.val.length ∧
    ∀ q ∈ out.val, Port3_FlushInstall.Canonical q := by
  have h : Port3_FlushInstall.flush b old = ok out := (reference_eq b old lengths).symm.trans success
  exact ⟨(Port3_FlushInstall.accepted_contents b old out lengths h).1,
    (Port3_FlushInstall.accepted_contents b old out lengths h).2,
    Port3_FlushInstall.accepted_canonical b old out lengths h⟩

def field (q : K) : AspisV8R15.ExactTowerBase.QM31Exact :=
  S8JoinFinishField.fieldValue (Port3_FlushInstall.toOwned q)

theorem row_field (row : S8OwnedP6ValueModel.Row) :
    field (Port3_FlushInstall.fromMutable (S8Kani2FinishReferenceJoin.toFinish (S8OwnedP6Finish.modelValue row))) =
      S8JoinFinishField.rawValue row := S8JoinFinishField.modelValue_field row

/-- Native finish preserves precisely the exact field value of every raw row;
canonicalization is allowed and no raw phase bound is required. -/
theorem accepted_field (b : verifier.BatchedWeights) (old out : Slice K)
    (lengths : old.val.length ≤ b.raw.val.length) (success : flush b old = ok out) :
    out.val.map field = (b.raw.val.take old.val.length).map S8JoinFinishField.rawValue := by
  rw [(accepted_rows b old out lengths success).1,List.map_map]
  apply List.map_congr_left
  intro row _
  exact row_field row

/-- Candidate replaces only the actual returned accumulator's weights. -/
def materialize (a : verifier.Accumulator) (out : Slice K) : verifier.Accumulator :=
  {a with weights := ⟨out.val,out.property⟩}

theorem materialize_fields (a : verifier.Accumulator) (out : Slice K) :
    (materialize a out).rhs = a.rhs ∧ (materialize a out).power = a.power ∧
    (materialize a out).next = a.next ∧ (materialize a out).weights.val = out.val :=
  ⟨rfl,rfl,rfl,rfl⟩

#print axioms lower_value
#print axioms accepted_rows
#print axioms row_field
#print axioms accepted_field
#print axioms materialize_fields
end AspisR1.Port4D_FlushRows
end
