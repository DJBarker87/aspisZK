import FIq_S_RawActualDecodeKPayloadBytes
set_option autoImplicit false
namespace AspisR1.FJq_CheckedOffset
open Aeneas Aeneas.Std Result
/-- Checked byte-offset computation retains its actual natural value. -/
theorem value (offset bytes : Usize)
    (run : lift (Usize.checked_mul offset 32#usize)=ok (some bytes)) :
    bytes.val=offset.val*32 := by
  have equation:=UScalar.mul_equiv offset (32#usize)
  cases called : UScalar.mul offset (32#usize) with
  | fail e =>
    simp only [Usize.checked_mul,core.num.checked_mul_UScalar,called,Option.ofResult,lift] at run
    cases run
  | div =>
    rw [called] at equation
    exact False.elim equation
  | ok out =>
    have same : out=bytes := by
      simpa only [Usize.checked_mul,core.num.checked_mul_UScalar,called,Option.ofResult,lift,
        Result.ok.injEq,Option.some.injEq] using run
    rw [called] at equation
    subst out
    exact equation.2.1
#print axioms value
end AspisR1.FJq_CheckedOffset
