import NFU_PacketDomains
set_option autoImplicit false
open Aeneas Aeneas.Std Result
namespace NFU_RowDomains
/-- The bound comes from the actual extracted helper, not an independent table. -/
theorem shape (row tag : U8) (size : Usize)
    (h : NFQ_Reference.row_shape_ref row = ok (some (tag,size))) :
    size.val ≤ 3712 ∧ size.val % 32 = 0 := by
  unfold NFQ_Reference.row_shape_ref at h
  split at h <;> simp_all
  all_goals repeat' (split at h <;> simp_all)

theorem parser_shape (row tag : U8) (size : Usize)
    (h : AspisR1PrefixAggregateParser.r1_wire.row_shape row = ok (some (tag,size))) :
    size.val ≤ 3712 ∧ size.val % 32 = 0 := by
  apply shape row tag size
  rw [NFQ_RowShape.prefix_reference]
  exact h

theorem framed (row tag : U8) (size : Usize) (bytes : Slice U8)
    (h : AspisR1PrefixAggregateParser.r1_wire.row_shape row = ok (some (tag,size)))
    (length : bytes.val.length = 5 + size.val) : bytes.val.length ≤ 3717 := by
  have bound := (parser_shape row tag size h).1
  omega
#print axioms shape
#print axioms parser_shape
#print axioms framed
end NFU_RowDomains
