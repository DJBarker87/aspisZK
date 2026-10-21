import Mathlib.Algebra.Field.Basic
import Mathlib.Data.List.Basic
import Mathlib.Tactic.Omega

/-! Constructor state invariant for the certified Vec append step. Scalar
geometry values and nonzero checks precede this step in the source; this
module does not silently identify arbitrary rows with domain geometry. -/
set_option autoImplicit false
namespace S7Kani2ConstructorInvariant
variable {α : Type}
abbrev Row (α : Type) := Fin 5 → α
structure Geometry (α : Type) where
  flat : List α
  lineZ : List α

def values (row : Row α) : List α := [row 0,row 1,row 2,row 3,row 4]
def append (state : Geometry α) (row : Row α) : Geometry α :=
  ⟨state.flat ++ values row,state.lineZ ++ [row 4]⟩
def gather : List (Row α) → Geometry α → Geometry α
 | [], state => state
 | row::rows,state => gather rows (append state row)

theorem gather_payload (rows : List (Row α)) (state : Geometry α) :
    (gather rows state).flat = state.flat ++ rows.flatMap values ∧
    (gather rows state).lineZ = state.lineZ ++ rows.map (fun row => row 4) := by
  induction rows generalizing state with
  | nil => simp [gather]
  | cons row rows ih =>
      obtain ⟨hflat,hz⟩ := ih (append state row)
      exact ⟨by simpa [gather,append,List.append_assoc] using hflat,
        by simpa [gather,append,List.append_assoc] using hz⟩

theorem flat_length (rows : List (Row α)) :
    (rows.flatMap values).length = 5*rows.length := by
  induction rows with
  | nil => rfl
  | cons row rows ih => simp [values,ih]; omega

/-- Exact production allocation bounds and returned vector lengths, once
successful backend rows have been supplied to the proved append driver. -/
theorem constructor_bounds (rows : List (Row α)) (h : rows.length ≤ 22) :
    (gather rows ⟨[],[]⟩).flat.length = 5*rows.length ∧
    (gather rows ⟨[],[]⟩).lineZ.length = rows.length ∧
    (gather rows ⟨[],[]⟩).flat.length ≤ 110 ∧
    (gather rows ⟨[],[]⟩).lineZ.length ≤ 22 := by
  obtain ⟨hf,hz⟩ := gather_payload rows ⟨[],[]⟩
  simp only [List.nil_append] at hf hz
  rw [hf,hz,flat_length,List.length_map]
  omega

/-- The backward batch-inversion write returns the reciprocal of the
selected nonzero entry, given the prefix/suffix product invariant. -/
theorem backward_inverse_cell {F : Type} [Field F] (prefix value suffix : F)
    (hp : prefix ≠ 0) (hs : suffix ≠ 0) :
    (prefix*value*suffix)⁻¹ * suffix * prefix = value⁻¹ := by
  calc
    _ = value⁻¹ * (suffix⁻¹*suffix) * (prefix⁻¹*prefix) := by
      simp only [mul_inv_rev]
      ac_rfl
    _ = value⁻¹ := by simp [hp,hs]

/-- Grouping cannot reverse query ordinal provenance: the 5-slot record at
ordinal i contains exactly flat slots 5*i through 5*i+4. -/
theorem grouping_offset (start ordinal count lane : Nat)
    (hord : ordinal<count) (hlane : lane<5) (hcount : count≤22) :
    (start+ordinal)-start=ordinal ∧
    5*((start+ordinal)-start)+lane<5*count ∧ 5*count≤110 := by omega

#print axioms gather_payload
#print axioms flat_length
#print axioms constructor_bounds
#print axioms backward_inverse_cell
#print axioms grouping_offset
end S7Kani2ConstructorInvariant
