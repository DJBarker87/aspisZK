import LIBC_Usize
import RSL_TX1_094
set_option autoImplicit false
namespace AspisR1.NNG_KGuard094
open Aeneas Aeneas.Std
/-- Out-of-carrier Nat inputs map to0, which preserves the source's sole
k=10 guard. No new bounded-k input clause is introduced. -/
theorem raw_eq_split (n : Nat) : LIBC_Usize.raw n=10#usize ↔ n=10 := by
 by_cases bound : n≤UScalar.cMax .Usize
 · constructor
   · intro equal
     have value := congrArg UScalar.val equal
     rw [LIBC_Usize.raw_val n bound] at value
     exact value
   · intro equal
     subst n
     exact LIBC_Usize.from_native 10#usize (by scalar_tac)
 · have zero : LIBC_Usize.raw n=0#usize := by
    unfold LIBC_Usize.raw
    rw [dif_neg bound]
   constructor
   · intro equal
     rw [zero] at equal
     have value := congrArg UScalar.val equal
     cases value
   · intro equal
     subst n
     exact False.elim (bound (by scalar_tac))
#print axioms raw_eq_split

theorem guard (n : Nat) : (LIBC_Usize.raw n != 10#usize) = (n != RSL.SPLIT) := by
 apply Bool.eq_iff_iff.mpr
 simpa only [bne_iff_ne,RSL.SPLIT] using not_congr (raw_eq_split n)
#print axioms guard
end AspisR1.NNG_KGuard094
