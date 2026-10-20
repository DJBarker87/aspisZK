set_option autoImplicit false

namespace AspisR1.S3S9CurrentSourceModel

def s2Row (j : Nat) : Nat :=
  (j % 4) * 64 + ((j / 4) % 4) * 256 +
  ((j / 16) % 4) * 16 + ((j / 64) % 4) + ((j / 256) % 4) * 4

/-- The five arithmetic contributions made by the exact S2 loop body emitted
from `Variant::row`. The array lookup uses `TAU = [3,4,2,0,1]`. -/
def s2RowLoopFormula (j : Nat) : Nat :=
  (j % 4) * 2^6 +
  ((j / 4) % 4) * 2^8 +
  ((j / 16) % 4) * 2^4 +
  ((j / 64) % 4) +
  ((j / 256) % 4) * 2^2

/-- Source-cut arithmetic for the S2 branch is exactly the current row model.
This isolates the numeric permutation from the Rust iterator/call boundary. -/
theorem s2_row_loop_formula_eq (j : Nat) :
    s2RowLoopFormula j = s2Row j := by
  simp [s2RowLoopFormula, s2Row]

end AspisR1.S3S9CurrentSourceModel

#print axioms AspisR1.S3S9CurrentSourceModel.s2_row_loop_formula_eq
