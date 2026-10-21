import MultiproofConeFrameHeader

set_option autoImplicit false
namespace AspisR1.MultiproofConeHeaderControl
open Aeneas Aeneas.Std Result
open MultiproofConeFrameHeader

/-- Exact early-return factoring of the inline extracted frame header. -/
theorem inline_eq {α : Type} (bytes : Slice U8) (tag : U8) (size : Usize)
    (k : Result (Option α)) :
    (do let b0 ← Slice.index_usize bytes 0#usize
        if b0 != tag then ok none else do
          let b1 ← Slice.index_usize bytes 1#usize
          let b2 ← Slice.index_usize bytes 2#usize
          let b3 ← Slice.index_usize bytes 3#usize
          let b4 ← Slice.index_usize bytes 4#usize
          let a := core.num.U32.to_le_bytes (UScalar.cast .U32 size)
          let ne ← core.array.equality.PartialEqArray.ne core.cmp.PartialEqU8
            (Array.make 4#usize [b1,b2,b3,b4]) a
          if ne then ok none else k) =
    (do let good ← headerChecks bytes tag size
        if good then k else ok none) := by
  unfold headerChecks
  cases h0 : Slice.index_usize bytes 0#usize with
  | fail e => rfl
  | div => rfl
  | ok b0 =>
    simp only [bind_tc_ok]
    by_cases mismatch : (b0 != tag)=true
    · simp only [mismatch,if_true,bind_tc_ok,Bool.false_eq_true,if_false]
    · simp only [mismatch,Bool.false_eq_true,if_false]
      cases h1 : Slice.index_usize bytes 1#usize with
      | fail e => rfl
      | div => rfl
      | ok b1 =>
        cases h2 : Slice.index_usize bytes 2#usize with
        | fail e => rfl
        | div => rfl
        | ok b2 =>
          cases h3 : Slice.index_usize bytes 3#usize with
          | fail e => rfl
          | div => rfl
          | ok b3 =>
            cases h4 : Slice.index_usize bytes 4#usize with
            | fail e => rfl
            | div => rfl
            | ok b4 =>
              simp only [bind_tc_ok]
              cases he : core.array.equality.PartialEqArray.ne core.cmp.PartialEqU8
                  (Array.make 4#usize [b1,b2,b3,b4])
                  (core.num.U32.to_le_bytes (UScalar.cast .U32 size)) with
              | fail e => rfl
              | div => rfl
              | ok ne => cases ne <;> simp only [bind_tc_ok,Bool.false_eq_true,if_false,if_true,Bool.not_false,Bool.not_true]

#print axioms inline_eq
end AspisR1.MultiproofConeHeaderControl
