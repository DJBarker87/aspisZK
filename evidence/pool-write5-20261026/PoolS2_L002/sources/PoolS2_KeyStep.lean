import PoolS2_UniqueSource
set_option autoImplicit false
namespace AspisR1.PoolS2_KeyStep
open Aeneas Aeneas.Std Result ControlFlow

theorem step (a b : Slice U8) (i : Usize) (x y : U8)
    (within : i < Slice.len a)
    (ra : Slice.index_usize a i = ok x) (rb : Slice.index_usize b i = ok y) :
    PoolS2_Unique.key_equal_loop.body a b i true =
      ok (cont (Usize.wrapping_add i 1#usize, decide (x = y))) := by
  simp [PoolS2_Unique.key_equal_loop.body,within,ra,rb,lift]

theorem stopped (a b : Slice U8) (i : Usize) :
    PoolS2_Unique.key_equal_loop.body a b i false = ok (done false) := by
  simp [PoolS2_Unique.key_equal_loop.body]

theorem ended (a b : Slice U8) (i : Usize) (equal : Bool)
    (outside : ¬ i < Slice.len a) :
    PoolS2_Unique.key_equal_loop.body a b i equal = ok (done equal) := by
  simp [PoolS2_Unique.key_equal_loop.body,outside]

#print axioms step
#print axioms stopped
#print axioms ended
end AspisR1.PoolS2_KeyStep
