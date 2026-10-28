import NCG_HornerLog
import LPi_RawValues
import LPi_PublicPush
set_option autoImplicit false
namespace NCG_TailLog
open Aeneas Aeneas.Std Result
open AspisR1.LPi_RawValues
/-- Opaque raw replies are substituted by the existing emitted raw value law.
This is an equality on the actual four-word reply carrier, not on an independently
selected product. The native logged-call association stays explicit. -/
theorem substitute (x y : Q) (hx : Canon x) (hy : Canon y)
    (a b c d : U64)
    (association : FIo_Native.fast_pairing.canonical.Q.raw x y =
      ok (Array.make 4#usize [a,b,c,d])) :
    (a.val,b.val,c.val,d.val) = spec x y := by
  obtain ⟨r0,r1,r2,r3,run,value⟩ := source x y hx hy
  have same := Result.ok.inj (association.symm.trans run)
  have words : [a,b,c,d] = [r0,r1,r2,r3] := congrArg (fun z => z.val) same
  simp only [List.cons.injEq, and_true] at words
  rcases words with ⟨rfl,rfl,rfl,rfl⟩
  exact value
#print axioms substitute
end NCG_TailLog
