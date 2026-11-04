import NFG_PrivateNative
import NFG_PublicG
import NFG_RawDomains
set_option autoImplicit false
noncomputable section
namespace AspisR1.NFG_PushRoot
open Aeneas Aeneas.Std Result NFG_PrivateWindow
abbrev Q := NFG_RawCoupling.Q
/-- Local observations acquired from one native raw call and the four
successive receiver states, rather than a whole-child output premise. -/
structure Cut (before : Dot) (a b : Q) where
 products : NFF_RawLog.Log
 law : ∀ i,NEG_ProductAbstraction.Product 64
  (NFF_RawLog.operands (NFF_RawTypedLog.words a) (NFF_RawTypedLog.words b) i).1
  (NFF_RawLog.operands (NFF_RawTypedLog.words a) (NFF_RawTypedLog.words b) i).2 (products i)
 raw : Raw
 rawNative : NFG_RawCoupling.values raw=NFF_RawLog.evaluate products
 s1 : Dot
 s2 : Dot
 s3 : Dot
 after : Dot
 w0 : Window before s1 raw ⟨0,by decide⟩
 w1 : Window s1 s2 raw ⟨1,by decide⟩
 w2 : Window s2 s3 raw ⟨2,by decide⟩
 w3 : Window s3 after raw ⟨3,by decide⟩
theorem private_result (before : Dot) (a b : Q)
 (ha : NFE_NFC_RawValues.Canon a) (hb : NFE_NFC_RawValues.Canon b)
 (cut : Cut before a b) :
 FIo_Native.fast_pairing.canonical.Dot.push before a b=ok cut.after :=
 NFG_PrivateNative.source a b ha hb cut.products cut.law cut.raw cut.rawNative
 before cut.s1 cut.s2 cut.s3 cut.after cut.w0 cut.w1 cut.w2 cut.w3

theorem private_domains (before : Dot) (a b : Q)
 (ha : NFE_NFC_RawValues.Canon a) (hb : NFE_NFC_RawValues.Canon b)
 (cut : Cut before a b) : ∀ i,cut.products i≤4611686009837453316 :=
 NFG_RawDomains.replies a b ha hb cut.products cut.law

theorem public_result (before : NFG_PublicG.Acc) (value : NEV_DotCarrier.NE) (scalar : NEV_DotCarrier.NQ)
 (canonical : NEV_DotCarrier.canonE value) (valid : NFG_PublicG.Valid scalar)
 (count : ¬before.count >= FIo_Native.fast_pairing.MAX_TERMS)
 (left : Cut before.c0 (NFE_NFC_CalleeDomains.q value.c0) (NFE_NFC_CalleeDomains.q scalar))
 (right : Cut before.c1 (NFE_NFC_CalleeDomains.q value.c1) (NFE_NFC_CalleeDomains.q scalar)) :
 FIo_Native.fast_pairing.EbyKDot.push before value scalar =
 ok (.Ok (),⟨left.after,right.after,Usize.wrapping_add before.count 1#usize⟩) := by
 obtain ⟨d0,d1,ds⟩ := NFG_PublicG.child_domains value scalar canonical valid
 rw [←NFG_PublicG.source]
 simp only [NFG_PublicG.run,count,ite_false,valid,ite_true,
  private_result before.c0 _ _ d0 ds left,private_result before.c1 _ _ d1 ds right,bind_tc_ok]
 rw [if_pos valid]

theorem reject_count (before : NFG_PublicG.Acc) (value : NEV_DotCarrier.NE) (scalar : NEV_DotCarrier.NQ)
 (count : before.count >= FIo_Native.fast_pairing.MAX_TERMS) :
 FIo_Native.fast_pairing.EbyKDot.push before value scalar=ok (.Err (),before) := by
 rw [←NFG_PublicG.source]
 simp only [NFG_PublicG.run,count,ite_true]

theorem reject_scalar (before : NFG_PublicG.Acc) (value : NEV_DotCarrier.NE) (scalar : NEV_DotCarrier.NQ)
 (invalid : ¬NFG_PublicG.Valid scalar) :
 FIo_Native.fast_pairing.EbyKDot.push before value scalar=ok (.Err (),before) := by
 rw [←NFG_PublicG.source]
 simp only [NFG_PublicG.run,invalid,ite_false]
 split <;> rfl
#print axioms private_result
#print axioms private_domains
#print axioms public_result
#print axioms reject_count
#print axioms reject_scalar
end AspisR1.NFG_PushRoot
end
