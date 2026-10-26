import R1Z.ProverRwDictionaryBytes
import R1Z.ProverCommitArray49
set_option autoImplicit false
namespace R1Z.ProverRwDictionaryLimbs
open Aeneas Aeneas.Std Result ProverRwFull
abbrev W := aspis_core.field.wide_exact.WideExact
abbrev P := ProverRwDictionaryBytesSource.aspis_core.field.P

def packed (w : Nat → U32) : W :=
  ⟨⟨⟨w 0,w 1⟩,⟨w 2,w 3⟩⟩,⟨⟨w 4,w 5⟩,⟨w 6,w 7⟩⟩⟩

def decode (w : Nat → U32) : Option W :=
  if w 0 >= P then none else
  if w 1 >= P then none else
  if w 2 >= P then none else
  if w 3 >= P then none else
  if w 4 >= P then none else
  if w 5 >= P then none else
  if w 6 >= P then none else
  if w 7 >= P then none else some (packed w)

theorem ok_if {A : Type} (p : Prop) [Decidable p] (x y : A) :
    (Result.ok (if p then x else y) : Result A) =
      (if p then .ok x else .ok y) := by split_ifs <;> rfl

/-- No input-success premise: all eight indices are in bounds. The actual
parser retains the first failed canonicality test, and has no machine failure. -/
theorem total (w : Nat → U32) :
    ProverRwDictionaryBytesSource.aspis_core.field.wide_exact.WideExact.from_limbs
      (ProverCommitArray49.array 8#usize w) = .ok (decode w) := by
  simp only [ProverRwDictionaryBytesSource.aspis_core.field.wide_exact.WideExact.from_limbs,
    ProverCommitArray49.index 8#usize w 0#usize (by decide),
    ProverCommitArray49.index 8#usize w 1#usize (by decide),
    ProverCommitArray49.index 8#usize w 2#usize (by decide),
    ProverCommitArray49.index 8#usize w 3#usize (by decide),
    ProverCommitArray49.index 8#usize w 4#usize (by decide),
    ProverCommitArray49.index 8#usize w 5#usize (by decide),
    ProverCommitArray49.index 8#usize w 6#usize (by decide),
    ProverCommitArray49.index 8#usize w 7#usize (by decide),bind_tc_ok]
  simp only [decode,packed,ok_if,
    show (0#usize).val = 0 by scalar_tac,
    show (1#usize).val = 1 by scalar_tac,
    show (2#usize).val = 2 by scalar_tac,
    show (3#usize).val = 3 by scalar_tac,
    show (4#usize).val = 4 by scalar_tac,
    show (5#usize).val = 5 by scalar_tac,
    show (6#usize).val = 6 by scalar_tac,
    show (7#usize).val = 7 by scalar_tac]

#print axioms ok_if
#print axioms total
end R1Z.ProverRwDictionaryLimbs
