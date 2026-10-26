import PoolW_ZeroSource
set_option autoImplicit false
namespace AspisR1.PoolW_ZeroStep
open Aeneas Aeneas.Std Result ControlFlow

theorem step (bytes : Slice U8) (i : Usize) (byte : U8)
    (within : i < Slice.len bytes) (read : Slice.index_usize bytes i = ok byte) :
    PoolW_Zero.zero_bytes_loop.body bytes i true =
      ok (cont (Usize.wrapping_add i 1#usize, decide (byte = 0#u8))) := by
  simp [PoolW_Zero.zero_bytes_loop.body, within, read, lift]

theorem stopped_false (bytes : Slice U8) (i : Usize) :
    PoolW_Zero.zero_bytes_loop.body bytes i false = ok (done false) := by
  simp [PoolW_Zero.zero_bytes_loop.body]

theorem exhausted (bytes : Slice U8) (i : Usize)
    (ended : ¬ i < Slice.len bytes) (zero : Bool) :
    PoolW_Zero.zero_bytes_loop.body bytes i zero = ok (done zero) := by
  simp [PoolW_Zero.zero_bytes_loop.body, ended]

#print axioms step
#print axioms stopped_false
#print axioms exhausted
end AspisR1.PoolW_ZeroStep
