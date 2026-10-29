import R1Z.PV_RDCD4_LazyProducts
set_option autoImplicit false
noncomputable section
namespace R1Z.PV_RDCD4_RadixBlock
open Aeneas Aeneas.Std Result PV_RDCD4_LazyComponents PV_RDCD4_LazyCell
abbrev Prepared := PV_RDCD4_FieldSource.aspis_core.field.PreparedQm31Multiplier
namespace F
abbrev square := PV_RDCD4_FieldSource.aspis_core.field.QM31.square
abbrev mul := PV_RDCD4_FieldSource.aspis_core.field.QM31.mul
abbrev add := PV_RDCD4_FieldSource.aspis_core.field.QM31.add
abbrev prepare := PV_RDCD4_FieldSource.aspis_core.field.PreparedQm31Multiplier.new
abbrev pmul := PV_RDCD4_FieldSource.aspis_core.field.PreparedQm31Multiplier.mul
end F
/-- Blocks are fixed-size arrays at the original interface; no coefficient
padding or scalar normalization is introduced. -/
def block (poly : Array Q 28#usize) (powers : Array Q 3#usize) (i : Nat) : Result Q := do
  let c0 ← read poly.val (4*i)
  let c1 ← read poly.val (4*i+1)
  let c2 ← read poly.val (4*i+2)
  let c3 ← read poly.val (4*i+3)
  let product ← PV_RDCD4_LazyProducts.source powers (Array.make 3#usize [c1,c2,c3])
  F.add c0 product

theorem index_bound (i offset : Nat) (hi : i < 7) (ho : offset < 4) :
    4*i+offset < 28 := by omega

theorem index_word_bound (i offset : Nat) (hi : i < 7) (ho : offset < 4) :
    4*i+offset < 2^64 := by
  have := index_bound i offset hi ho
  omega
#print axioms index_bound
#print axioms index_word_bound
end R1Z.PV_RDCD4_RadixBlock
