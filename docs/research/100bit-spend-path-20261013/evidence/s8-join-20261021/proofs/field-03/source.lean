import S8JoinFinishExact
import ExtractedCurrentQM31Exact

/-! Finish is the identity on the exact quartic field represented by each
raw row. The U64-to-U32 canonical reduction is proved, not a backend premise. -/
set_option autoImplicit false
noncomputable section
namespace AspisR1.S8JoinFinishField
open Aeneas Aeneas.Std Result
open AspisV8R15.ExactTowerBase
open S8OwnedP6ValueModel S8OwnedP6Finish

/-- Decode the literal source coordinate order into the retained exact tower. -/
def fieldValue (q : Q) : QM31Exact :=
  ⟨⟨(q.c0.a.val : M31Exact),(q.c0.b.val : M31Exact)⟩,
    ⟨(q.c1.a.val : M31Exact),(q.c1.b.val : M31Exact)⟩⟩

def rawValue (row : Row) : QM31Exact :=
  ⟨⟨((rowAt row 0).val : M31Exact),((rowAt row 1).val : M31Exact)⟩,
    ⟨((rowAt row 2).val : M31Exact),((rowAt row 3).val : M31Exact)⟩⟩

/-- No raw phase bound: reduction preserves all four exact field coordinates. -/
theorem modelValue_field (row : Row) : fieldValue (modelValue row) = rawValue row := by
  have c0 := (modelValue_coordinates row 0).1
  have c1 := (modelValue_coordinates row 1).1
  have c2 := (modelValue_coordinates row 2).1
  have c3 := (modelValue_coordinates row 3).1
  change (modelValue row).c0.a.val = (rowAt row 0).val%2147483647 at c0
  change (modelValue row).c0.b.val = (rowAt row 1).val%2147483647 at c1
  change (modelValue row).c1.a.val = (rowAt row 2).val%2147483647 at c2
  change (modelValue row).c1.b.val = (rowAt row 3).val%2147483647 at c3
  simp only [fieldValue,rawValue,c0,c1,c2,c3]
  congr 2 <;> simp [M31Exact,P,ZMod.natCast_mod]

/-- Total emitted reference output has exactly the raw field values. -/
theorem finish_field (raw : Raw) (old : Weights) (lengths : old.length ≤ raw.length) :
    ∃ out : Weights, S8OwnedP6.finish_owned raw old = .ok out ∧
      out.length=old.length ∧
      out.val.map fieldValue = (raw.val.take old.length).map rawValue := by
  refine ⟨S8JoinFinishExact.output raw old,S8JoinFinishExact.reference_exact raw old lengths,?_,?_⟩
  · simp [S8JoinFinishExact.output, Nat.min_eq_left lengths]
  · simp only [S8JoinFinishExact.output,List.map_map]
    apply List.map_congr_left
    intro row _
    exact modelValue_field row

#print axioms modelValue_field
#print axioms finish_field
end AspisR1.S8JoinFinishField
end
