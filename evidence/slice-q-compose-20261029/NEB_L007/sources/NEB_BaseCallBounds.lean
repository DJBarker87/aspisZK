import NEB_CMCalls
set_option autoImplicit false
namespace NEB_BaseCallBounds
open Aeneas Aeneas.Std Result AspisR1 LPi_FieldValues

/-- Both deployed canonical branches avoid the raw fallback and checked
arithmetic overflow. This is a bound on the actual native scalar expressions. -/
theorem add (a b : U32) (ha : a.val<2147483647) (hb : b.val<2147483647) :
    a.val+b.val < 4294967296 ∧ a.val+b.val ≤ 4294967295 ∧
      a.val+b.val < 2*2147483647 := by omega

theorem sub (a b : U32) (ha : a.val<2147483647) (hb : b.val<2147483647) :
    a.val+2147483647 < 4294967296 ∧ b.val ≤ a.val+2147483647 ∧
      a.val+2147483647-b.val < 2*2147483647 := by omega

/-- Full raw-u32 products fit: the M31 product packet has no hidden canonical
operand requirement. The reducer packet accepts every U64. -/
theorem raw_product (a b : U32) : a.val*b.val < 18446744073709551616 := by
  have ha : a.val<4294967296 := a.hSize
  have hb : b.val<4294967296 := b.hSize
  have h := Nat.mul_lt_mul_of_lt_of_lt ha hb
  exact h

theorem multiply_reducer (a b : U32) :
    ∃ z,
      FIo_Native.aspis_core.field.M31.mul a b=ok z ∧
      z.val=(a.val*b.val)%2147483647 ∧ z.val<2147483647 :=
  LPf_BaseMultiply.source a b

theorem reducer (x : U64) :
    ∃ z,FIo_Native.aspis_core.field.reduce_u64 x=ok z ∧
      z.val=x.val%2147483647 ∧ z.val<2147483647 :=
  LPf_CoreReduction.source x

/-- Wrapper has exactly the same input and return, with no arithmetic
precondition added at the root-to-reducer edge. -/
theorem reducer_wrapper (x : U64) :
    FIo_Native.aspis_core.field.M31.reduce_u64 x =
      FIo_Native.aspis_core.field.reduce_u64 x := by
  simp only [FIo_Native.aspis_core.field.M31.reduce_u64,bind_tc_ok]

#print axioms add
#print axioms sub
#print axioms raw_product
#print axioms multiply_reducer
#print axioms reducer
#print axioms reducer_wrapper
end NEB_BaseCallBounds
