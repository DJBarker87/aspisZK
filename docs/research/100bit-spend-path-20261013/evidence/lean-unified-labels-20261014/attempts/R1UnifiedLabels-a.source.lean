import R1OpeningReseedFrame

/-! Symbolic 33-row byte-label schedule. This does not assert a correspondence
with a protocol parameter's label function. -/
set_option autoImplicit false
noncomputable section
namespace AspisR1.UnifiedLabels

open AspisV8R19.DuplexFrames

def label (n : Nat) : Byte :=
  ⟨(160 + n) % 256, Nat.mod_lt _ (by decide)⟩

theorem label_val (n : Nat) (hn : n < 33) : (label n).val = 160 + n := by
  simp only [label, Fin.val_mk]
  rw [Nat.mod_eq_of_lt]
  omega

theorem label_zero : label 0 = 160 := by
  apply Fin.ext
  simp [label]

theorem label_injective {i j : Nat} (hi : i < 33) (hj : j < 33)
    (h : label i = label j) : i = j := by
  have hv := congrArg Fin.val h
  rw [label_val i hi, label_val j hj] at hv
  omega

def row (b : Byte) : Nat := b.val - 160

theorem row_label (n : Nat) (hn : n < 33) : row (label n) = n := by
  simp [row, label_val n hn]

#print axioms label_val
#print axioms label_zero
#print axioms label_injective
#print axioms row_label

end AspisR1.UnifiedLabels
end
