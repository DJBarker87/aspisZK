import MultiproofConeCodec
import MultiproofParserRef.Funs

set_option autoImplicit false
namespace AspisR1.MultiproofConeRowShape
open Aeneas Aeneas.Std Result
open OraclePortCompactDraft

theorem shape_properties (row : Nat) :
    (rowShape row).1 ≤ 5 ∧ (rowShape row).2 ≤ 3712 ∧ (rowShape row).2 % 32 = 0 := by
  unfold rowShape
  split_ifs <;> decide

theorem shape_total (row : U8) (bound : row.val < 27) :
    ∃ tag size, MultiproofParserRef.reference.row_shape row = ok (some (tag,size)) ∧
      tag.val = (rowShape row.val).1 ∧ size.val = (rowShape row.val).2 := by
  have h := MultiproofConeCodec.row_shape_total row bound
  have same : MultiproofConeRef.reference.row_shape row =
      MultiproofParserRef.reference.row_shape row := rfl
  rw [same] at h
  cases he : MultiproofParserRef.reference.row_shape row with
  | fail e => simp only [he,bind_tc_fail] at h; cases h
  | div => simp only [he,bind_tc_div] at h; cases h
  | ok result =>
    simp only [he,bind_tc_ok] at h
    cases result with
    | none => cases h
    | some pair =>
      rcases pair with ⟨tag,size⟩
      have eq : (tag.val,size.val) = rowShape row.val := Option.some.inj (Result.ok.inj h)
      exact ⟨tag,size,rfl,congrArg Prod.fst eq,congrArg Prod.snd eq⟩

#print axioms shape_properties
#print axioms shape_total
end AspisR1.MultiproofConeRowShape
