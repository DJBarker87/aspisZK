import PV_B3P_MatrixStore14227
import PV_B3P_Ordered227
namespace PV_B3P_Binding14227
open Aeneas Aeneas.Std Result
set_option autoImplicit false
abbrev Write14 := Usize × Usize × U64
/-- Every prefix snapshot is retained; this is stronger than final equality. -/
def matrix_trace14 (write : Matrix14 → Usize → Usize → U64 → Result Matrix14) :
    List Write14 → Matrix14 → Result (List Matrix14)
  | [], sums => .ok [sums]
  | (row,column,value)::rest, sums => do
      let next ← write sums row column value
      let tail ← matrix_trace14 write rest next
      .ok (sums::tail)

def MatrixWritesBound14 (writes : List Write14) : Prop :=
  ∀ row column value, (row,column,value) ∈ writes → row.val < 3 ∧ column.val < 3

theorem matrix_trace_binding14 (writes : List Write14) (sums : Matrix14)
    (bound : MatrixWritesBound14 writes) :
    matrix_trace14 source_matrix_store14 writes sums =
      matrix_trace14 model_matrix_store14 writes sums := by
  induction writes generalizing sums with
  | nil => rfl
  | cons entry rest ih =>
    rcases entry with ⟨row,column,value⟩
    have b := bound row column value (by simp only [List.mem_cons]; exact Or.inl rfl)
    have br : MatrixWritesBound14 rest := by
      intro r c v mem
      exact bound r c v (by simp only [List.mem_cons]; exact Or.inr mem)
    simp only [matrix_trace14,matrix_store_binding14 sums row column value b.1 b.2]
    cases h : model_matrix_store14 sums row column value with
    | fail e => rfl
    | div => rfl
    | ok next => simp only [bind_tc_ok,ih next br]
#print axioms matrix_trace_binding14
end PV_B3P_Binding14227
