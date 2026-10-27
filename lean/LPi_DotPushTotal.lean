import LPi_RawValues
import LPf_DotPushCut
import LPf_ArrayFour
set_option autoImplicit false
namespace AspisR1.LPi_DotPushTotal
open Aeneas Aeneas.Std Result

theorem source (self : FIo_Native.fast_pairing.canonical.Dot)
    (a b : LPi_RawValues.Q) (ha : LPi_RawValues.Canon a) (hb : LPi_RawValues.Canon b) :
    ∃ out, FIo_Native.fast_pairing.canonical.Dot.push self a b=ok out := by
  obtain ⟨s0,s1,s2,s3,shape⟩ := LPf_ArrayFour.shape self.sums
  obtain ⟨r0,r1,r2,r3,raw,_⟩ := LPi_RawValues.source a b ha hb
  have same : self=⟨Array.make 4#usize [s0,s1,s2,s3]⟩ := by
    cases self
    exact congrArg FIo_Native.fast_pairing.canonical.Dot.mk shape
  subst self
  exact ⟨_,LPf_DotPushCut.source a b s0 s1 s2 s3 r0 r1 r2 r3 raw⟩

#print axioms source
end AspisR1.LPi_DotPushTotal
