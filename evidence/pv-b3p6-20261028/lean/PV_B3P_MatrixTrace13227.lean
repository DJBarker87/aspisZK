import PV_B3P_MatrixStore13227
namespace PV_B3P_Binding13227
open Aeneas Aeneas.Std Result
set_option autoImplicit false
abbrev MatrixWrite13 := Usize × Usize × U64

def record_matrix_stores13
    (store : Matrix13 → Usize → Usize → U64 → Result Matrix13) :
    Matrix13 → List MatrixWrite13 → Result (List Matrix13)
  | _, [] => .ok []
  | sums, write::writes => do
      let next ← store sums write.1 write.2.1 write.2.2
      let tail ← record_matrix_stores13 store next writes
      .ok (next::tail)

def PV_B3P_Link_matrix_trace
    (native : Matrix13 → Usize → Usize → U64 → Result Matrix13) : Prop :=
  ∀ sums writes, (∀ write ∈ writes, write.1.val < 3 ∧ write.2.1.val < 3) →
    record_matrix_stores13 native sums writes = record_matrix_stores13 model_matrix_store13 sums writes

theorem matrix_trace_from_stores13
    (native : Matrix13 → Usize → Usize → U64 → Result Matrix13)
    (stores : PV_B3P_Link_matrix_stores native) : PV_B3P_Link_matrix_trace native := by
  intro sums writes valid
  induction writes generalizing sums with
  | nil => rfl
  | cons write writes ih =>
    have h := valid write (by simp only [List.mem_cons]; exact Or.inl rfl)
    simp only [record_matrix_stores13,stores sums write.1 write.2.1 write.2.2 h.1 h.2]
    apply congrArg (Aeneas.Std.bind _)
    funext next
    rw [ih next (fun w hw => valid w (by simp only [List.mem_cons]; exact Or.inr hw))]

theorem source_matrix_trace_link13 : PV_B3P_Link_matrix_trace source_matrix_store13 :=
  matrix_trace_from_stores13 source_matrix_store13 matrix_stores_link13
#print axioms matrix_trace_from_stores13
#print axioms source_matrix_trace_link13
end PV_B3P_Binding13227
