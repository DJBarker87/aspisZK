import AspisV8R17.SourceMinor
import AspisV8R17.MatrixWindow
import Mathlib.Data.ZMod.Basic

/-! Nat indexing is only a wrapper for consecutive finite windows. Every
in-bounds application is identified with the same ordered source minor. -/
set_option autoImplicit false
namespace AspisV8R17.SourceMinor

def sourceMatrix (i j : ℕ) : ZMod 2147483647 :=
  orderedMinor 1073741824 2 13 11 (-7)
    ⟨i%214, Nat.mod_lt _ (by decide)⟩ ⟨j%214, Nat.mod_lt _ (by decide)⟩

theorem sourceMatrix_at (i j : ℕ) (hi : i<214) (hj : j<214) :
    sourceMatrix i j = orderedMinor (1073741824 : ZMod 2147483647) 2 13 11 (-7)
      ⟨i,hi⟩ ⟨j,hj⟩ := by
  simp only [sourceMatrix, Nat.mod_eq_of_lt hi, Nat.mod_eq_of_lt hj]

theorem full_window_eq : matrixWindow sourceMatrix 0 214 =
    orderedMinor (1073741824 : ZMod 2147483647) 2 13 11 (-7) := by
  ext i j
  simpa only [matrixWindow, Nat.zero_add] using sourceMatrix_at i.val j.val i.isLt j.isLt

#print axioms sourceMatrix_at
#print axioms full_window_eq
end AspisV8R17.SourceMinor
