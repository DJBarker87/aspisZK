import NFF_RawTypedLog
import NFE_NFC_DotPushCut
set_option autoImplicit false
namespace AspisR1.NFI_PrivateCuts
open Aeneas Aeneas.Std Result

/-- One raw reply, derived from sixteen same-operand natural products, is
threaded through the four actual receiver iterations. No independently chosen
post-receiver is a hypothesis. The existing loop chain supplies the induction. -/
theorem installed (a b : NFE_NFC_RawValues.Q)
    (ha : NFE_NFC_RawValues.Canon a) (hb : NFE_NFC_RawValues.Canon b)
    (s0 s1 s2 s3 : U64) (p : NFF_RawLog.Log)
    (law : ∀ i,NEG_ProductAbstraction.Product 64
      (NFF_RawLog.operands (NFF_RawTypedLog.words a) (NFF_RawTypedLog.words b) i).1
      (NFF_RawLog.operands (NFF_RawTypedLog.words a) (NFF_RawTypedLog.words b) i).2 (p i)) :
    ∃ r0 r1 r2 r3 : U64,
      FIo_Native.fast_pairing.canonical.Q.raw a b=ok (Array.make 4#usize [r0,r1,r2,r3]) ∧
      (r0.val,r1.val,r2.val,r3.val)=NFF_RawLog.evaluate p ∧
      FIo_Native.fast_pairing.canonical.Dot.push
        ⟨Array.make 4#usize [s0,s1,s2,s3]⟩ a b =
        ok ⟨Array.make 4#usize [NFE_NFC_DotPushFour.update s0 r0,
          NFE_NFC_DotPushFour.update s1 r1,NFE_NFC_DotPushFour.update s2 r2,
          NFE_NFC_DotPushFour.update s3 r3]⟩ := by
  obtain ⟨r0,r1,r2,r3,raw,value⟩ := NFF_RawTypedLog.replay a b ha hb p law
  exact ⟨r0,r1,r2,r3,raw,value,
    NFE_NFC_DotPushCut.source a b s0 s1 s2 s3 r0 r1 r2 r3 raw⟩

#print axioms installed
end AspisR1.NFI_PrivateCuts
