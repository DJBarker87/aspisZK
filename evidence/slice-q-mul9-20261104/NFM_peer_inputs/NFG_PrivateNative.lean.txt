import NFG_RawCoupling
import NFG_PrivateTrace
set_option autoImplicit false
noncomputable section
namespace AspisR1.NFG_PrivateNative
open Aeneas Aeneas.Std Result NFG_PrivateWindow
/-- Source-to-model assembly for ONE native raw call followed by the SAME four
receiver states. Every hypothesis names a local native assertion, not a whole
callee output or an independently chosen successful execution. The hybrid
certificate instantiates them from NFF_K019/021/068 on the fixed source loop. -/
theorem source (a b : NFG_RawCoupling.Q)
 (ha : NFE_NFC_RawValues.Canon a) (hb : NFE_NFC_RawValues.Canon b)
 (products : NFF_RawLog.Log)
 (law : ∀ i,NEG_ProductAbstraction.Product 64
  (NFF_RawLog.operands (NFF_RawTypedLog.words a) (NFF_RawTypedLog.words b) i).1
  (NFF_RawLog.operands (NFF_RawTypedLog.words a) (NFF_RawTypedLog.words b) i).2 (products i))
 (raw : Raw) (rawNative : NFG_RawCoupling.values raw=NFF_RawLog.evaluate products)
 (s0 s1 s2 s3 s4 : Dot)
 (w0 : Window s0 s1 raw ⟨0,by decide⟩)
 (w1 : Window s1 s2 raw ⟨1,by decide⟩)
 (w2 : Window s2 s3 raw ⟨2,by decide⟩)
 (w3 : Window s3 s4 raw ⟨3,by decide⟩) :
 FIo_Native.fast_pairing.canonical.Dot.push s0 a b=ok s4 := by
 have rawCall:=NFG_RawCoupling.native_result a b ha hb products law raw rawNative
 unfold FIo_Native.fast_pairing.canonical.Dot.push
 rw [rawCall,bind_tc_ok]
 exact NFG_PrivateTrace.four raw s0 s1 s2 s3 s4 w0 w1 w2 w3
#print axioms source
end AspisR1.NFG_PrivateNative
end
