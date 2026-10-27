import FIo_ScalarBridge
set_option autoImplicit false
namespace AspisR1.FJm_WrappingSuccess
open Aeneas Aeneas.Std Result

theorem add (a b z : U64) (h : a+b=ok z) : U64.wrapping_add a b=z := by
  have bound : a.val+b.val<UScalar.size .U64 := by
    change UScalar.add a b=ok z at h
    unfold UScalar.add UScalar.tryMk UScalar.tryMkOpt at h
    split at h
    · rename_i hb
      scalar_tac
    · cases h
  exact Result.ok.inj ((FIo_ScalarBridge.add a b bound).symm.trans h)

theorem sub (a b z : U64) (h : a-b=ok z) : U64.wrapping_sub a b=z := by
  have bound : b.val≤a.val := by
    change UScalar.sub a b=ok z at h
    unfold UScalar.sub at h
    split at h
    · cases h
    · omega
  exact Result.ok.inj ((FIo_ScalarBridge.sub a b bound).symm.trans h)

theorem mul (a b z : U64) (h : a*b=ok z) : U64.wrapping_mul a b=z := by
  have bound : a.val*b.val<UScalar.size .U64 := by
    change UScalar.mul a b=ok z at h
    unfold UScalar.mul UScalar.tryMk UScalar.tryMkOpt at h
    split at h
    · rename_i hb
      scalar_tac
    · cases h
  exact Result.ok.inj ((FIo_ScalarBridge.mul a b bound).symm.trans h)
#print axioms add
#print axioms sub
#print axioms mul
end AspisR1.FJm_WrappingSuccess
