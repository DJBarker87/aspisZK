import NJB_StateUpdates
set_option autoImplicit false
namespace AspisR1.NJL_WriteFrame
variable {I V : Type} [DecidableEq I]
def write (s : I → V) (i : I) (v : V) : I → V := fun j=>if i=j then v else s j
/-- Finite frame composition for repeated writes of the SAME per-cell value.
No buffer payload is inferred from an address; every untouched cell is framed. -/
theorem fold (values : I → V) (xs : List I) (s : I → V) (j : I) :
 (xs.foldl (fun before i=>write before i (values i)) s) j=
 if j∈xs then values j else s j := by
 induction xs generalizing s with
 | nil => simp
 | cons i xs ih =>
  rw [List.foldl_cons,ih]
  by_cases h : j∈xs
  · simp [h]
  · by_cases same : i=j
    · subst i;simp [h,write]
    · have other : j≠i := Ne.symm same
      simp [h,same,other,write]
#print axioms fold
end AspisR1.NJL_WriteFrame
