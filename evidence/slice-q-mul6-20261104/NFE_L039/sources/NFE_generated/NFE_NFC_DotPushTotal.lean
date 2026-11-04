import NFE_NFC_RawValues
import NFE_NFC_DotPushCut
import NFC_ArrayFour
set_option autoImplicit false
namespace AspisR1.NFE_NFC_DotPushTotal
open Aeneas Aeneas.Std Result

theorem source (self : FIo_Native.fast_pairing.canonical.Dot)
    (a b : NFE_NFC_RawValues.Q) (ha : NFE_NFC_RawValues.Canon a) (hb : NFE_NFC_RawValues.Canon b) :
    ∃ out, FIo_Native.fast_pairing.canonical.Dot.push self a b=ok out := by
  obtain ⟨s0,s1,s2,s3,shape⟩ := NFC_ArrayFour.shape self.sums
  obtain ⟨r0,r1,r2,r3,raw,_⟩ := NFE_NFC_RawValues.source a b ha hb
  have same : self=⟨Array.make 4#usize [s0,s1,s2,s3]⟩ := by
    cases self
    exact congrArg FIo_Native.fast_pairing.canonical.Dot.mk shape
  subst self
  exact ⟨_,NFE_NFC_DotPushCut.source a b s0 s1 s2 s3 r0 r1 r2 r3 raw⟩

#print axioms source
end AspisR1.NFE_NFC_DotPushTotal
