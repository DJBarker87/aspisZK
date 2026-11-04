import Lean
import NFY_Part037
import NFY_Part033
import NFY_Part020
import NFY_Part034
import NFY_Part021
import NFY_Part032
import NFY_Part024
import S6ZeroWordBytesV1
import NFY_Part023
import RPz7_S6NativePaymentAcceptedInverseV1
import RPz7_S6NativeLateEncodeSuccessV1

-- BEGIN copied JFs_PaymentDigests: lean/JFs_PaymentDigests.lean
set_option autoImplicit false
namespace AspisR1.NFY_JFs_PaymentDigests
open Aeneas Aeneas.Std Result
open AspisR1TerminalDecoder

def bytes43 : Array U8 32#usize := ⟨NFY_JFu_PublicDigest43.bytes,NFY_JFu_PublicDigest43.length⟩
theorem selected43 : (NFY_JFu_PublicRange.segment 1744 32 (by decide)).val=bytes43.val := by
  dsimp only [NFY_JFu_PublicRange.segment,bytes43]
  exact NFY_JFu_PublicDigest43.selected
theorem shared43 : core.array.TryFromSharedArraySlice.try_from 32#usize
    (NFY_JFu_PublicRange.segment 1744 32 (by decide))=ok (.Ok bytes43) :=
  NFY_JFt_DigestArray.shared _ _ selected43
theorem decode43 : atomic_statement.decode_digest_canonical bytes43=ok (.Ok NFY_JFt_Digest43.value) :=
  NFY_JFt_DigestArray.source _ _ selected43 _ NFY_JFt_Digest43.source

def bytes44 : Array U8 32#usize := ⟨NFY_JFu_PublicDigest44.bytes,NFY_JFu_PublicDigest44.length⟩
theorem selected44 : (NFY_JFu_PublicRange.segment 1776 32 (by decide)).val=bytes44.val := by
  dsimp only [NFY_JFu_PublicRange.segment,bytes44]
  exact NFY_JFu_PublicDigest44.selected
theorem shared44 : core.array.TryFromSharedArraySlice.try_from 32#usize
    (NFY_JFu_PublicRange.segment 1776 32 (by decide))=ok (.Ok bytes44) :=
  NFY_JFt_DigestArray.shared _ _ selected44
theorem decode44 : atomic_statement.decode_digest_canonical bytes44=ok (.Ok NFY_JFt_Digest44.value) :=
  NFY_JFt_DigestArray.source _ _ selected44 _ NFY_JFt_Digest44.source

def bytes45 : Array U8 32#usize := ⟨NFY_JFu_PublicDigest45.bytes,NFY_JFu_PublicDigest45.length⟩
theorem selected45 : (NFY_JFu_PublicRange.segment 1816 32 (by decide)).val=bytes45.val := by
  dsimp only [NFY_JFu_PublicRange.segment,bytes45]
  exact NFY_JFu_PublicDigest45.selected
theorem shared45 : core.array.TryFromSharedArraySlice.try_from 32#usize
    (NFY_JFu_PublicRange.segment 1816 32 (by decide))=ok (.Ok bytes45) :=
  NFY_JFt_DigestArray.shared _ _ selected45
theorem decode45 : atomic_statement.decode_digest_canonical bytes45=ok (.Ok NFY_JFt_Digest45.value) :=
  NFY_JFt_DigestArray.source _ _ selected45 _ NFY_JFt_Digest45.source

def bytes46 : Array U8 32#usize := ⟨NFY_JFu_PublicDigest46.bytes,NFY_JFu_PublicDigest46.length⟩
theorem selected46 : (NFY_JFu_PublicRange.segment 1848 32 (by decide)).val=bytes46.val := by
  dsimp only [NFY_JFu_PublicRange.segment,bytes46]
  exact NFY_JFu_PublicDigest46.selected
theorem shared46 : core.array.TryFromSharedArraySlice.try_from 32#usize
    (NFY_JFu_PublicRange.segment 1848 32 (by decide))=ok (.Ok bytes46) :=
  NFY_JFt_DigestArray.shared _ _ selected46
theorem decode46 : atomic_statement.decode_digest_canonical bytes46=ok (.Ok NFY_JFt_Digest46.value) :=
  NFY_JFt_DigestArray.source _ _ selected46 _ NFY_JFt_Digest46.source

#print axioms selected43
#print axioms shared43
#print axioms decode43
#print axioms selected44
#print axioms shared44
#print axioms decode44
#print axioms selected45
#print axioms shared45
#print axioms decode45
#print axioms selected46
#print axioms shared46
#print axioms decode46
end AspisR1.NFY_JFs_PaymentDigests
-- END copied JFs_PaymentDigests
-- BEGIN copied JFs_Cell04: lean/JFs_Cell04.lean
set_option autoImplicit false
namespace AspisR1.NFY_JFs_Cell04
open Aeneas Aeneas.Std Result

def bytes : List U8 := [34#u8,8#u8,198#u8,55#u8,61#u8,211#u8,19#u8,178#u8,242#u8,118#u8,165#u8,45#u8,20#u8,254#u8,147#u8,25#u8,55#u8,157#u8,211#u8,124#u8,152#u8,170#u8,59#u8,88#u8,182#u8,77#u8,252#u8,152#u8,45#u8,26#u8,82#u8,63#u8]
theorem length : bytes.length=32 := by simp only [bytes,List.length_cons,List.length_nil]

theorem selected : (NFY_JFx_NativeBytes.publicInput.val.drop 1672).take 32=bytes := by
  change (NFY_JFx_DataPublic00.bytes.drop 1672).take 32=bytes
  simp only [NFY_JFx_DataPublic00.bytes,NFY_JFx_DataPublic00.c00_length,NFY_JFx_DataPublic00.c01_length,NFY_JFx_DataPublic00.c02_length,NFY_JFx_DataPublic00.c03_length,NFY_JFx_DataPublic00.c04_length,NFY_JFx_DataPublic00.c05_length,NFY_JFx_DataPublic00.c06_length,NFY_JFx_DataPublic00.c07_length,NFY_JFx_DataPublic00.c08_length,NFY_JFx_DataPublic00.c09_length,NFY_JFx_DataPublic00.c10_length,NFY_JFx_DataPublic00.c11_length,NFY_JFx_DataPublic00.c12_length,NFY_JFx_DataPublic00.c13_length,NFY_JFx_DataPublic00.c14_length,NFY_JFx_DataPublic00.c15_length,NFY_JFx_DataPublic00.c16_length,NFY_JFx_DataPublic00.c17_length,NFY_JFx_DataPublic00.c18_length,NFY_JFx_DataPublic00.c19_length,NFY_JFx_DataPublic00.c20_length,NFY_JFx_DataPublic00.c21_length,NFY_JFx_DataPublic00.c22_length,NFY_JFx_DataPublic00.c23_length,NFY_JFx_DataPublic00.c24_length,NFY_JFx_DataPublic00.c25_length,NFY_JFx_DataPublic00.c26_length,NFY_JFx_DataPublic00.c27_length,NFY_JFx_DataPublic00.c28_length,NFY_JFx_DataPublic00.c29_length,NFY_JFx_DataPublic00.c30_length,NFY_JFx_DataPublic00.c31_length,NFY_JFx_DataPublic00.c32_length,NFY_JFx_DataPublic00.c33_length,NFY_JFx_DataPublic00.c34_length,NFY_JFx_DataPublic00.c35_length,NFY_JFx_DataPublic00.c36_length,NFY_JFx_DataPublic00.c37_length,NFY_JFx_DataPublic00.c38_length,NFY_JFx_DataPublic00.c39_length,NFY_JFx_DataPublic00.c40_length,NFY_JFx_DataPublic00.c41_length,NFY_JFx_DataPublic00.c42_length,NFY_JFx_DataPublic00.c43_length,NFY_JFx_DataPublic00.c44_length,NFY_JFx_DataPublic00.c45_length,NFY_JFx_DataPublic00.c46_length,NFY_JFx_DataPublic00.c47_length,NFY_JFx_DataPublic00.c48_length,NFY_JFx_DataPublic00.c49_length,NFY_JFx_DataPublic00.c50_length,NFY_JFx_DataPublic00.c51_length,NFY_JFx_DataPublic00.c52_length,NFY_JFx_DataPublic00.c53_length,NFY_JFx_DataPublic00.c54_length,NFY_JFx_DataPublic00.c55_length,NFY_JFx_DataPublic00.c56_length,NFY_JFx_DataPublic00.c57_length,NFY_JFx_DataPublic00.c58_length,List.drop_append,List.take_append,List.length_append,Nat.reduceAdd,Nat.reduceSub,Nat.reduceLeDiff,List.length_drop,List.drop_eq_nil_of_le,List.take_of_length_le,List.drop_zero,List.take_zero,List.nil_append,List.append_nil]
  rfl

theorem source : core.slice.index.Slice.index (core.slice.index.SliceIndexRangeUsizeSlice U8)
    NFY_JFx_NativeBytes.publicInput {start:=1672#usize,«end»:=1704#usize}=
    ok (NFY_JFu_PublicRange.segment 1672 32 (by decide)) :=
  by
    have call:=NFY_JFu_PublicRange.read 1672#usize 1704#usize (by decide) (by decide)
    simpa only [show (1672#usize).val=1672 from rfl,
      show (1704#usize).val=1704 from rfl,Nat.reduceSub] using call

def value : Array U8 32#usize := ⟨bytes,length⟩

#print axioms length
#print axioms selected
#print axioms source
end AspisR1.NFY_JFs_Cell04
-- END copied JFs_Cell04
-- BEGIN copied JFs_Cell05: lean/JFs_Cell05.lean
set_option autoImplicit false
namespace AspisR1.NFY_JFs_Cell05
open Aeneas Aeneas.Std Result

def bytes : List U8 := [5#u8,5#u8,5#u8,5#u8,5#u8,5#u8,5#u8,5#u8,5#u8,5#u8,5#u8,5#u8,5#u8,5#u8,5#u8,5#u8,5#u8,5#u8,5#u8,5#u8,5#u8,5#u8,5#u8,5#u8,5#u8,5#u8,5#u8,5#u8,5#u8,5#u8,5#u8,5#u8]
theorem length : bytes.length=32 := by simp only [bytes,List.length_cons,List.length_nil]

theorem selected : (NFY_JFx_NativeBytes.publicInput.val.drop 1704).take 32=bytes := by
  change (NFY_JFx_DataPublic00.bytes.drop 1704).take 32=bytes
  simp only [NFY_JFx_DataPublic00.bytes,NFY_JFx_DataPublic00.c00_length,NFY_JFx_DataPublic00.c01_length,NFY_JFx_DataPublic00.c02_length,NFY_JFx_DataPublic00.c03_length,NFY_JFx_DataPublic00.c04_length,NFY_JFx_DataPublic00.c05_length,NFY_JFx_DataPublic00.c06_length,NFY_JFx_DataPublic00.c07_length,NFY_JFx_DataPublic00.c08_length,NFY_JFx_DataPublic00.c09_length,NFY_JFx_DataPublic00.c10_length,NFY_JFx_DataPublic00.c11_length,NFY_JFx_DataPublic00.c12_length,NFY_JFx_DataPublic00.c13_length,NFY_JFx_DataPublic00.c14_length,NFY_JFx_DataPublic00.c15_length,NFY_JFx_DataPublic00.c16_length,NFY_JFx_DataPublic00.c17_length,NFY_JFx_DataPublic00.c18_length,NFY_JFx_DataPublic00.c19_length,NFY_JFx_DataPublic00.c20_length,NFY_JFx_DataPublic00.c21_length,NFY_JFx_DataPublic00.c22_length,NFY_JFx_DataPublic00.c23_length,NFY_JFx_DataPublic00.c24_length,NFY_JFx_DataPublic00.c25_length,NFY_JFx_DataPublic00.c26_length,NFY_JFx_DataPublic00.c27_length,NFY_JFx_DataPublic00.c28_length,NFY_JFx_DataPublic00.c29_length,NFY_JFx_DataPublic00.c30_length,NFY_JFx_DataPublic00.c31_length,NFY_JFx_DataPublic00.c32_length,NFY_JFx_DataPublic00.c33_length,NFY_JFx_DataPublic00.c34_length,NFY_JFx_DataPublic00.c35_length,NFY_JFx_DataPublic00.c36_length,NFY_JFx_DataPublic00.c37_length,NFY_JFx_DataPublic00.c38_length,NFY_JFx_DataPublic00.c39_length,NFY_JFx_DataPublic00.c40_length,NFY_JFx_DataPublic00.c41_length,NFY_JFx_DataPublic00.c42_length,NFY_JFx_DataPublic00.c43_length,NFY_JFx_DataPublic00.c44_length,NFY_JFx_DataPublic00.c45_length,NFY_JFx_DataPublic00.c46_length,NFY_JFx_DataPublic00.c47_length,NFY_JFx_DataPublic00.c48_length,NFY_JFx_DataPublic00.c49_length,NFY_JFx_DataPublic00.c50_length,NFY_JFx_DataPublic00.c51_length,NFY_JFx_DataPublic00.c52_length,NFY_JFx_DataPublic00.c53_length,NFY_JFx_DataPublic00.c54_length,NFY_JFx_DataPublic00.c55_length,NFY_JFx_DataPublic00.c56_length,NFY_JFx_DataPublic00.c57_length,NFY_JFx_DataPublic00.c58_length,List.drop_append,List.take_append,List.length_append,Nat.reduceAdd,Nat.reduceSub,Nat.reduceLeDiff,List.length_drop,List.drop_eq_nil_of_le,List.take_of_length_le,List.drop_zero,List.take_zero,List.nil_append,List.append_nil]
  rfl

theorem source : core.slice.index.Slice.index (core.slice.index.SliceIndexRangeUsizeSlice U8)
    NFY_JFx_NativeBytes.publicInput {start:=1704#usize,«end»:=1736#usize}=
    ok (NFY_JFu_PublicRange.segment 1704 32 (by decide)) :=
  by
    have call:=NFY_JFu_PublicRange.read 1704#usize 1736#usize (by decide) (by decide)
    simpa only [show (1704#usize).val=1704 from rfl,
      show (1736#usize).val=1736 from rfl,Nat.reduceSub] using call

def value : Array U8 32#usize := ⟨bytes,length⟩

#print axioms length
#print axioms selected
#print axioms source
end AspisR1.NFY_JFs_Cell05
-- END copied JFs_Cell05
-- BEGIN copied JFs_Cell06: lean/JFs_Cell06.lean
set_option autoImplicit false
namespace AspisR1.NFY_JFs_Cell06
open Aeneas Aeneas.Std Result

def bytes : List U8 := [42#u8,0#u8,0#u8,0#u8,0#u8,0#u8,0#u8,0#u8]
theorem length : bytes.length=8 := by simp only [bytes,List.length_cons,List.length_nil]

theorem selected : (NFY_JFx_NativeBytes.publicInput.val.drop 1736).take 8=bytes := by
  change (NFY_JFx_DataPublic00.bytes.drop 1736).take 8=bytes
  simp only [NFY_JFx_DataPublic00.bytes,NFY_JFx_DataPublic00.c00_length,NFY_JFx_DataPublic00.c01_length,NFY_JFx_DataPublic00.c02_length,NFY_JFx_DataPublic00.c03_length,NFY_JFx_DataPublic00.c04_length,NFY_JFx_DataPublic00.c05_length,NFY_JFx_DataPublic00.c06_length,NFY_JFx_DataPublic00.c07_length,NFY_JFx_DataPublic00.c08_length,NFY_JFx_DataPublic00.c09_length,NFY_JFx_DataPublic00.c10_length,NFY_JFx_DataPublic00.c11_length,NFY_JFx_DataPublic00.c12_length,NFY_JFx_DataPublic00.c13_length,NFY_JFx_DataPublic00.c14_length,NFY_JFx_DataPublic00.c15_length,NFY_JFx_DataPublic00.c16_length,NFY_JFx_DataPublic00.c17_length,NFY_JFx_DataPublic00.c18_length,NFY_JFx_DataPublic00.c19_length,NFY_JFx_DataPublic00.c20_length,NFY_JFx_DataPublic00.c21_length,NFY_JFx_DataPublic00.c22_length,NFY_JFx_DataPublic00.c23_length,NFY_JFx_DataPublic00.c24_length,NFY_JFx_DataPublic00.c25_length,NFY_JFx_DataPublic00.c26_length,NFY_JFx_DataPublic00.c27_length,NFY_JFx_DataPublic00.c28_length,NFY_JFx_DataPublic00.c29_length,NFY_JFx_DataPublic00.c30_length,NFY_JFx_DataPublic00.c31_length,NFY_JFx_DataPublic00.c32_length,NFY_JFx_DataPublic00.c33_length,NFY_JFx_DataPublic00.c34_length,NFY_JFx_DataPublic00.c35_length,NFY_JFx_DataPublic00.c36_length,NFY_JFx_DataPublic00.c37_length,NFY_JFx_DataPublic00.c38_length,NFY_JFx_DataPublic00.c39_length,NFY_JFx_DataPublic00.c40_length,NFY_JFx_DataPublic00.c41_length,NFY_JFx_DataPublic00.c42_length,NFY_JFx_DataPublic00.c43_length,NFY_JFx_DataPublic00.c44_length,NFY_JFx_DataPublic00.c45_length,NFY_JFx_DataPublic00.c46_length,NFY_JFx_DataPublic00.c47_length,NFY_JFx_DataPublic00.c48_length,NFY_JFx_DataPublic00.c49_length,NFY_JFx_DataPublic00.c50_length,NFY_JFx_DataPublic00.c51_length,NFY_JFx_DataPublic00.c52_length,NFY_JFx_DataPublic00.c53_length,NFY_JFx_DataPublic00.c54_length,NFY_JFx_DataPublic00.c55_length,NFY_JFx_DataPublic00.c56_length,NFY_JFx_DataPublic00.c57_length,NFY_JFx_DataPublic00.c58_length,List.drop_append,List.take_append,List.length_append,Nat.reduceAdd,Nat.reduceSub,Nat.reduceLeDiff,List.length_drop,List.drop_eq_nil_of_le,List.take_of_length_le,List.drop_zero,List.take_zero,List.nil_append,List.append_nil]
  rfl

theorem source : core.slice.index.Slice.index (core.slice.index.SliceIndexRangeUsizeSlice U8)
    NFY_JFx_NativeBytes.publicInput {start:=1736#usize,«end»:=1744#usize}=
    ok (NFY_JFu_PublicRange.segment 1736 8 (by decide)) :=
  by
    have call:=NFY_JFu_PublicRange.read 1736#usize 1744#usize (by decide) (by decide)
    simpa only [show (1736#usize).val=1736 from rfl,
      show (1744#usize).val=1744 from rfl,Nat.reduceSub] using call

def value : Array U8 8#usize := ⟨bytes,length⟩

#print axioms length
#print axioms selected
#print axioms source
end AspisR1.NFY_JFs_Cell06
-- END copied JFs_Cell06
-- BEGIN copied JFs_Cell07: lean/JFs_Cell07.lean
set_option autoImplicit false
namespace AspisR1.NFY_JFs_Cell07
open Aeneas Aeneas.Std Result

def bytes : List U8 := [77#u8,0#u8,0#u8,0#u8]
theorem length : bytes.length=4 := by simp only [bytes,List.length_cons,List.length_nil]

theorem selected : (NFY_JFx_NativeBytes.publicInput.val.drop 1808).take 4=bytes := by
  change (NFY_JFx_DataPublic00.bytes.drop 1808).take 4=bytes
  simp only [NFY_JFx_DataPublic00.bytes,NFY_JFx_DataPublic00.c00_length,NFY_JFx_DataPublic00.c01_length,NFY_JFx_DataPublic00.c02_length,NFY_JFx_DataPublic00.c03_length,NFY_JFx_DataPublic00.c04_length,NFY_JFx_DataPublic00.c05_length,NFY_JFx_DataPublic00.c06_length,NFY_JFx_DataPublic00.c07_length,NFY_JFx_DataPublic00.c08_length,NFY_JFx_DataPublic00.c09_length,NFY_JFx_DataPublic00.c10_length,NFY_JFx_DataPublic00.c11_length,NFY_JFx_DataPublic00.c12_length,NFY_JFx_DataPublic00.c13_length,NFY_JFx_DataPublic00.c14_length,NFY_JFx_DataPublic00.c15_length,NFY_JFx_DataPublic00.c16_length,NFY_JFx_DataPublic00.c17_length,NFY_JFx_DataPublic00.c18_length,NFY_JFx_DataPublic00.c19_length,NFY_JFx_DataPublic00.c20_length,NFY_JFx_DataPublic00.c21_length,NFY_JFx_DataPublic00.c22_length,NFY_JFx_DataPublic00.c23_length,NFY_JFx_DataPublic00.c24_length,NFY_JFx_DataPublic00.c25_length,NFY_JFx_DataPublic00.c26_length,NFY_JFx_DataPublic00.c27_length,NFY_JFx_DataPublic00.c28_length,NFY_JFx_DataPublic00.c29_length,NFY_JFx_DataPublic00.c30_length,NFY_JFx_DataPublic00.c31_length,NFY_JFx_DataPublic00.c32_length,NFY_JFx_DataPublic00.c33_length,NFY_JFx_DataPublic00.c34_length,NFY_JFx_DataPublic00.c35_length,NFY_JFx_DataPublic00.c36_length,NFY_JFx_DataPublic00.c37_length,NFY_JFx_DataPublic00.c38_length,NFY_JFx_DataPublic00.c39_length,NFY_JFx_DataPublic00.c40_length,NFY_JFx_DataPublic00.c41_length,NFY_JFx_DataPublic00.c42_length,NFY_JFx_DataPublic00.c43_length,NFY_JFx_DataPublic00.c44_length,NFY_JFx_DataPublic00.c45_length,NFY_JFx_DataPublic00.c46_length,NFY_JFx_DataPublic00.c47_length,NFY_JFx_DataPublic00.c48_length,NFY_JFx_DataPublic00.c49_length,NFY_JFx_DataPublic00.c50_length,NFY_JFx_DataPublic00.c51_length,NFY_JFx_DataPublic00.c52_length,NFY_JFx_DataPublic00.c53_length,NFY_JFx_DataPublic00.c54_length,NFY_JFx_DataPublic00.c55_length,NFY_JFx_DataPublic00.c56_length,NFY_JFx_DataPublic00.c57_length,NFY_JFx_DataPublic00.c58_length,List.drop_append,List.take_append,List.length_append,Nat.reduceAdd,Nat.reduceSub,Nat.reduceLeDiff,List.length_drop,List.drop_eq_nil_of_le,List.take_of_length_le,List.drop_zero,List.take_zero,List.nil_append,List.append_nil]
  rfl

theorem source : core.slice.index.Slice.index (core.slice.index.SliceIndexRangeUsizeSlice U8)
    NFY_JFx_NativeBytes.publicInput {start:=1808#usize,«end»:=1812#usize}=
    ok (NFY_JFu_PublicRange.segment 1808 4 (by decide)) :=
  by
    have call:=NFY_JFu_PublicRange.read 1808#usize 1812#usize (by decide) (by decide)
    simpa only [show (1808#usize).val=1808 from rfl,
      show (1812#usize).val=1812 from rfl,Nat.reduceSub] using call

def value : Array U8 4#usize := ⟨bytes,length⟩

#print axioms length
#print axioms selected
#print axioms source
end AspisR1.NFY_JFs_Cell07
-- END copied JFs_Cell07
-- BEGIN copied JFs_PaymentCanon: lean/JFs_PaymentCanon.lean
set_option autoImplicit false
namespace AspisR1.NFY_JFs_PaymentCanon
open Aeneas Aeneas.Std Result WP
open AspisR1TerminalDecoder

theorem source (digest : Array U32 8#usize) (canon : NFY_JFu_DigestCanonical.Canonical digest) :
    pool_v1.payment_relation.digest_is_canonical digest=ok true := by
  have c0:=canon ⟨0,by decide⟩
  have c1:=canon ⟨1,by decide⟩
  have c2:=canon ⟨2,by decide⟩
  have c3:=canon ⟨3,by decide⟩
  have c4:=canon ⟨4,by decide⟩
  have c5:=canon ⟨5,by decide⟩
  have c6:=canon ⟨6,by decide⟩
  have c7:=canon ⟨7,by decide⟩
  have spec : pool_v1.payment_relation.digest_is_canonical digest ⦃ b => b=true ⦄ := by
    unfold pool_v1.payment_relation.digest_is_canonical
    step*
    all_goals unfold aspis_core.field.P at *
    all_goals simp_all [NFY_JFu_DigestCanonical.Canonical]
    all_goals scalar_tac
  obtain ⟨b,call,same⟩:=WP.spec_imp_exists spec
  rw [same] at call
  exact call

#print axioms source
end AspisR1.NFY_JFs_PaymentCanon
-- END copied JFs_PaymentCanon
-- BEGIN copied JFs_PaymentValue: lean/JFs_PaymentValue.lean
set_option autoImplicit false
namespace AspisR1.NFY_JFs_PaymentValue
open Aeneas Aeneas.Std Result
open AspisR1TerminalDecoder pool_v1.payment_relation

def common : CommonPublicV1 :=
  {pool:=NFY_JFs_Cell04.value,deployment_domain:=NFY_JFs_Cell05.value,
   anchor_sequence:=core.num.U64.from_le_bytes NFY_JFs_Cell06.value,
   anchor_root:=NFY_JFt_Digest43.value,nullifier:=NFY_JFt_Digest44.value,
   asset_id:=core.num.U32.from_le_bytes NFY_JFs_Cell07.value}

def value : PoolV1PrivateTransferPublicV1 :=
  {pool:=common.pool,deployment_domain:=common.deployment_domain,
   anchor_sequence:=common.anchor_sequence,anchor_root:=common.anchor_root,
   nullifier:=common.nullifier,asset_id:=common.asset_id,
   recipient_commitment:=NFY_JFt_Digest45.value,change_commitment:=NFY_JFt_Digest46.value}

theorem sequence : core.num.U64.from_le_bytes NFY_JFs_Cell06.value=42#u64 := by rfl
theorem asset : core.num.U32.from_le_bytes NFY_JFs_Cell07.value=77#u32 := by rfl

theorem pool_nonzero : core.array.equality.PartialEqArray.eq core.cmp.PartialEqU8
    NFY_JFs_Cell04.value (Array.repeat 32#usize 0#u8)=ok false := by rfl
theorem domain_nonzero : core.array.equality.PartialEqArray.eq core.cmp.PartialEqU8
    NFY_JFs_Cell05.value (Array.repeat 32#usize 0#u8)=ok false := by rfl

theorem common_validated : validate_common common=ok (.Ok ()) := by
  unfold validate_common common
  simp only [pool_nonzero,domain_nonzero,bind_tc_ok,Bool.false_eq_true,↓reduceIte,sequence,asset,
    NFY_JFs_PaymentCanon.source _ NFY_JFt_Digest43.canonical,
    NFY_JFs_PaymentCanon.source _ NFY_JFt_Digest44.canonical]
  unfold pool_v1.incremental_merkle.POOL_V1_LEAF_CAPACITY pool_v1.format.POOL_V1_TREE_DEPTH aspis_core.field.P
  rfl

theorem validated : validate_pool_v1_private_transfer_public_v1 value=ok (.Ok ()) := by
  unfold validate_pool_v1_private_transfer_public_v1
  have transfer : transfer_common value=ok common := by rfl
  rw [transfer,bind_tc_ok,common_validated]
  simp only [bind_tc_ok,core.result.Result.Insts.CoreOpsTry.branch,
    value,NFY_JFs_PaymentCanon.source _ NFY_JFt_Digest45.canonical,
    NFY_JFs_PaymentCanon.source _ NFY_JFt_Digest46.canonical,Bool.true_eq,↓reduceIte]

#print axioms sequence
#print axioms asset
#print axioms pool_nonzero
#print axioms domain_nonzero
#print axioms common_validated
#print axioms validated
end AspisR1.NFY_JFs_PaymentValue
-- END copied JFs_PaymentValue
-- BEGIN copied JFt_Digest00: lean/JFt_Digest00.lean
set_option autoImplicit false
namespace AspisR1.NFY_JFt_Digest00
open Aeneas Aeneas.Std Result

def value : Array AspisR1TerminalDecoder.aspis_core.field.M31 8#usize :=
  Array.make 8#usize [71235157#u32,561336479#u32,2021715933#u32,831357912#u32,593948515#u32,110335229#u32,1732475008#u32,949858646#u32]

/-- Exact numeric value is identified by the symbolic byte-injectivity lemma. -/
theorem local_call : AspisS6NativeSnapshotReadDigest.read_digest NFY_JFu_PublicDigest00.window=ok (.Ok value) := by
  obtain ⟨out,call,canon,contents⟩:=NFY_JFu_DigestSliceFacts.source NFY_JFu_PublicDigest00.window
    NFY_JFu_PublicDigest00.length NFY_JFu_PublicDigest00.canonical_bytes
  have bytes : AspisS6SourceCodec.DigestContents.chunks value=NFY_JFu_PublicDigest00.bytes := by
    simp [AspisS6SourceCodec.DigestContents.chunks,value,Array.make,core.num.U32.to_le_bytes,BitVec.toLEBytes,NFY_JFu_PublicDigest00.bytes]
    <;> (repeat' constructor) <;> scalar_tac
  have same : out=value := NFY_JFt_DigestInjective.injective out value (contents.trans bytes.symm)
  rw [same] at call
  exact call

theorem selected : NFY_JFu_PublicRange.segment 112 32 (by decide)=NFY_JFu_PublicDigest00.window := by
  apply Subtype.ext
  exact NFY_JFu_PublicDigest00.selected

theorem source : AspisS6NativeSnapshotReadDigest.read_digest
    (NFY_JFu_PublicRange.segment 112 32 (by decide))=ok (.Ok value) := by
  rw [selected]
  exact local_call

theorem canonical : NFY_JFu_DigestCanonical.Canonical value :=
  NFY_JFu_DigestSliceCanonical.source _ _ source

#print axioms local_call
#print axioms selected
#print axioms source
#print axioms canonical
end AspisR1.NFY_JFt_Digest00
-- END copied JFt_Digest00
-- BEGIN copied JFs_PublicValue: lean/JFs_PublicValue.lean
set_option autoImplicit false
namespace AspisR1.NFY_JFs_PublicValue
open Aeneas Aeneas.Std Result
open AspisR1TerminalDecoder pool_v1.pair_forest_terminal

def common : PoolV1PairForestTerminalCommonV1 :=
  {master_account:=NFY_JFs_Cell00.value,checkpoint_account:=NFY_JFs_Cell01.value,
   selected_lane_account:=NFY_JFs_Cell02.value,output_lane:=3#u8,
   checkpoint_sequence:=core.num.U64.from_le_bytes NFY_JFs_Cell03.value,
   historical_global_anchor:=NFY_JFt_Digest00.value,lane_transition:=NFY_JFs_LateChildren.value}

def value : PoolV1PairForestTerminalStatementV1 := .PrivateTransfer common NFY_JFs_PaymentValue.value

theorem sequence : core.num.U64.from_le_bytes NFY_JFs_Cell03.value=42#u64 := by rfl

theorem payment_pool : NFY_JFs_PaymentValue.common.pool=common.master_account := by rfl

theorem snapshot_pool : NFY_JFt_SnapshotValue.value.pool=common.master_account := by rfl

theorem payment_domain : NFY_JFs_PaymentValue.common.deployment_domain=
    NFY_JFt_SnapshotValue.value.deployment_domain := by rfl

theorem anchor : NFY_JFt_Digest43.value=common.historical_global_anchor := by rfl

theorem master_nonzero : core.array.equality.PartialEqArray.eq core.cmp.PartialEqU8
    common.master_account (Array.repeat 32#usize 0#u8)=ok false := by rfl

theorem checkpoint_nonzero : core.array.equality.PartialEqArray.eq core.cmp.PartialEqU8
    common.checkpoint_account (Array.repeat 32#usize 0#u8)=ok false := by rfl

theorem lane_nonzero : core.array.equality.PartialEqArray.eq core.cmp.PartialEqU8
    common.selected_lane_account (Array.repeat 32#usize 0#u8)=ok false := by rfl

#print axioms sequence
#print axioms payment_pool
#print axioms snapshot_pool
#print axioms payment_domain
#print axioms anchor
#print axioms master_nonzero
#print axioms checkpoint_nonzero
#print axioms lane_nonzero
end AspisR1.NFY_JFs_PublicValue
-- END copied JFs_PublicValue
-- BEGIN copied JFs_PublicComparisons: lean/JFs_PublicComparisons.lean
set_option autoImplicit false
namespace AspisR1.NFY_JFs_PublicComparisons
open Aeneas Aeneas.Std Result
open AspisR1TerminalDecoder

theorem pool : core.array.equality.PartialEqArray.ne core.cmp.PartialEqU8
    NFY_JFs_PaymentValue.common.pool NFY_JFs_PublicValue.common.master_account=ok false := by rfl

theorem domain : core.array.equality.PartialEqArray.ne core.cmp.PartialEqU8
    NFY_JFs_PaymentValue.common.deployment_domain
    NFY_JFs_PublicValue.common.lane_transition.live_snapshot.deployment_domain=ok false := by rfl

theorem snapshot_pool : core.array.equality.PartialEqArray.ne core.cmp.PartialEqU8
    NFY_JFs_PublicValue.common.lane_transition.live_snapshot.pool
    NFY_JFs_PublicValue.common.master_account=ok false := by rfl

theorem anchor : core.array.equality.PartialEqArray.ne aspis_core.field.M31.Insts.CoreCmpPartialEqM31
    NFY_JFs_PaymentValue.common.anchor_root NFY_JFs_PublicValue.common.historical_global_anchor=ok false := by rfl

theorem sequence : (NFY_JFs_PaymentValue.common.anchor_sequence !=NFY_JFs_PublicValue.common.checkpoint_sequence)=false := by rfl

theorem lane_bound : ¬(core.convert.num.FromUsizeU8.from NFY_JFs_PublicValue.common.output_lane >=
    pool_v1.pair_forest_accounts.POOL_V1_PAIR_FOREST_LANE_COUNT) := by
  unfold pool_v1.pair_forest_accounts.POOL_V1_PAIR_FOREST_LANE_COUNT
    core.convert.num.FromUsizeU8.from
  change ¬(UScalar.cast .Usize 3#u8 >=8#usize)
  scalar_tac

theorem lane : (3#u8 !=NFY_JFs_PublicValue.common.output_lane)=false := by rfl

#print axioms pool
#print axioms domain
#print axioms snapshot_pool
#print axioms anchor
#print axioms sequence
#print axioms lane_bound
#print axioms lane
end AspisR1.NFY_JFs_PublicComparisons
-- END copied JFs_PublicComparisons
-- BEGIN copied JFs_ArrayWindow: lean/JFs_ArrayWindow.lean
set_option autoImplicit false
namespace AspisR1.NFY_JFs_ArrayWindow
open Aeneas Aeneas.Std Result

def array (off : Nat) (n : Usize) (bound : off+n.val≤1880) : Array U8 n :=
  ⟨(NFY_JFu_PublicRange.segment off n.val bound).val,NFY_JFu_PublicRange.length off n.val bound⟩

theorem range (off : Nat) (n : Usize) (bound : off+n.val≤1880) (start stop : Usize)
    (order : start.val≤stop.val) (inside : stop.val≤n.val) :
    core.array.Array.index
      (core.ops.index.IndexSlice (core.slice.index.SliceIndexRangeUsizeSlice U8))
      (array off n bound) {start:=start,«end»:=stop}=
      ok (NFY_JFu_PublicRange.segment (off+start.val) (stop.val-start.val) (by omega)) := by
  unfold core.array.Array.index core.ops.index.IndexSlice array
  exact NFY_JFt_Range.read off n.val bound start stop order inside

theorem suffix (off : Nat) (n : Usize) (bound : off+n.val≤1880) (start : Usize)
    (inside : start.val≤n.val) :
    core.array.Array.index
      (core.ops.index.IndexSlice (core.slice.index.SliceIndexRangeFromUsizeSlice U8))
      (array off n bound) {start:=start}=
      ok (NFY_JFu_PublicRange.segment (off+start.val) (n.val-start.val) (by omega)) := by
  unfold core.array.Array.index core.ops.index.IndexSlice array
  exact NFY_JFs_RangeFrom.read off n.val bound start inside

theorem shared (N : Usize) (bytes : Slice U8) (arr : Array U8 N) (same : bytes.val=arr.val) :
    core.array.TryFromSharedArraySlice.try_from N bytes=ok (.Ok arr) := by
  have size : Slice.len bytes=N := by
    have h : bytes.length=N.val := by change bytes.val.length=N.val;rw [same,arr.property]
    scalar_tac
  unfold core.array.TryFromSharedArraySlice.try_from
  rw [dif_pos size]
  apply congrArg ok
  apply congrArg core.result.Result.Ok
  exact Subtype.ext same

#print axioms range
#print axioms suffix
#print axioms shared
end AspisR1.NFY_JFs_ArrayWindow
-- END copied JFs_ArrayWindow
-- BEGIN copied JFu_PublicMeta07: lean/JFu_PublicMeta07.lean
set_option autoImplicit false
namespace AspisR1.NFY_JFu_PublicMeta07
open Aeneas Aeneas.Std Result

def bytes : List U8 := [65#u8,83#u8,67#u8,80#u8,1#u8,1#u8,1#u8,0#u8]
theorem length : bytes.length=8 := by simp only [bytes,List.length_cons,List.length_nil]

theorem selected : (NFY_JFx_NativeBytes.publicInput.val.drop 1664).take 8=bytes := by
  change (NFY_JFx_DataPublic00.bytes.drop 1664).take 8=bytes
  simp only [NFY_JFx_DataPublic00.bytes,NFY_JFx_DataPublic00.c00_length,NFY_JFx_DataPublic00.c01_length,NFY_JFx_DataPublic00.c02_length,NFY_JFx_DataPublic00.c03_length,NFY_JFx_DataPublic00.c04_length,NFY_JFx_DataPublic00.c05_length,NFY_JFx_DataPublic00.c06_length,NFY_JFx_DataPublic00.c07_length,NFY_JFx_DataPublic00.c08_length,NFY_JFx_DataPublic00.c09_length,NFY_JFx_DataPublic00.c10_length,NFY_JFx_DataPublic00.c11_length,NFY_JFx_DataPublic00.c12_length,NFY_JFx_DataPublic00.c13_length,NFY_JFx_DataPublic00.c14_length,NFY_JFx_DataPublic00.c15_length,NFY_JFx_DataPublic00.c16_length,NFY_JFx_DataPublic00.c17_length,NFY_JFx_DataPublic00.c18_length,NFY_JFx_DataPublic00.c19_length,NFY_JFx_DataPublic00.c20_length,NFY_JFx_DataPublic00.c21_length,NFY_JFx_DataPublic00.c22_length,NFY_JFx_DataPublic00.c23_length,NFY_JFx_DataPublic00.c24_length,NFY_JFx_DataPublic00.c25_length,NFY_JFx_DataPublic00.c26_length,NFY_JFx_DataPublic00.c27_length,NFY_JFx_DataPublic00.c28_length,NFY_JFx_DataPublic00.c29_length,NFY_JFx_DataPublic00.c30_length,NFY_JFx_DataPublic00.c31_length,NFY_JFx_DataPublic00.c32_length,NFY_JFx_DataPublic00.c33_length,NFY_JFx_DataPublic00.c34_length,NFY_JFx_DataPublic00.c35_length,NFY_JFx_DataPublic00.c36_length,NFY_JFx_DataPublic00.c37_length,NFY_JFx_DataPublic00.c38_length,NFY_JFx_DataPublic00.c39_length,NFY_JFx_DataPublic00.c40_length,NFY_JFx_DataPublic00.c41_length,NFY_JFx_DataPublic00.c42_length,NFY_JFx_DataPublic00.c43_length,NFY_JFx_DataPublic00.c44_length,NFY_JFx_DataPublic00.c45_length,NFY_JFx_DataPublic00.c46_length,NFY_JFx_DataPublic00.c47_length,NFY_JFx_DataPublic00.c48_length,NFY_JFx_DataPublic00.c49_length,NFY_JFx_DataPublic00.c50_length,NFY_JFx_DataPublic00.c51_length,NFY_JFx_DataPublic00.c52_length,NFY_JFx_DataPublic00.c53_length,NFY_JFx_DataPublic00.c54_length,NFY_JFx_DataPublic00.c55_length,NFY_JFx_DataPublic00.c56_length,NFY_JFx_DataPublic00.c57_length,NFY_JFx_DataPublic00.c58_length,List.drop_append,List.take_append,List.length_append,Nat.reduceAdd,Nat.reduceSub,Nat.reduceLeDiff,List.length_drop,List.drop_eq_nil_of_le,List.take_of_length_le,List.drop_zero,List.take_zero,List.nil_append,List.append_nil]
  rfl

theorem source : core.slice.index.Slice.index (core.slice.index.SliceIndexRangeUsizeSlice U8)
    NFY_JFx_NativeBytes.publicInput {start:=1664#usize,«end»:=1672#usize}=
    ok (NFY_JFu_PublicRange.segment 1664 8 (by decide)) :=
  by
    have call:=NFY_JFu_PublicRange.read 1664#usize 1672#usize (by decide) (by decide)
    simpa only [show (1664#usize).val=1664 from rfl,
      show (1672#usize).val=1672 from rfl,Nat.reduceSub] using call

#print axioms length
#print axioms selected
#print axioms source
end AspisR1.NFY_JFu_PublicMeta07
-- END copied JFu_PublicMeta07
-- BEGIN copied JFs_PaymentArray: lean/JFs_PaymentArray.lean
set_option autoImplicit false
namespace AspisR1.NFY_JFs_PaymentArray
open Aeneas Aeneas.Std Result

def value : Array U8 216#usize := NFY_JFs_ArrayWindow.array 1664 216#usize (by decide)

theorem shared : core.array.TryFromSharedArraySlice.try_from 216#usize NFY_JFu_PublicRange.payment=
    ok (.Ok value) := by
  apply NFY_JFs_ArrayWindow.shared
  simp only [value,NFY_JFs_ArrayWindow.array,NFY_JFu_PublicRange.payment,show (216#usize).val=216 from rfl]

theorem range (start stop : Usize) (order : start.val≤stop.val) (inside : stop.val≤216) :
    core.array.Array.index
      (core.ops.index.IndexSlice (core.slice.index.SliceIndexRangeUsizeSlice U8))
      value {start:=start,«end»:=stop}=
      ok (NFY_JFu_PublicRange.segment (1664+start.val) (stop.val-start.val) (by omega)) :=
  NFY_JFs_ArrayWindow.range 1664 216#usize (by decide) start stop order inside

theorem suffix (start : Usize) (inside : start.val≤216) :
    core.array.Array.index
      (core.ops.index.IndexSlice (core.slice.index.SliceIndexRangeFromUsizeSlice U8))
      value {start:=start}=
      ok (NFY_JFu_PublicRange.segment (1664+start.val) (216-start.val) (by omega)) :=
  NFY_JFs_ArrayWindow.suffix 1664 216#usize (by decide) start inside

#print axioms shared
#print axioms range
#print axioms suffix
end AspisR1.NFY_JFs_PaymentArray
-- END copied JFs_PaymentArray
-- BEGIN copied JFu_PublicMeta08: lean/JFu_PublicMeta08.lean
set_option autoImplicit false
namespace AspisR1.NFY_JFu_PublicMeta08
open Aeneas Aeneas.Std Result

def bytes : List U8 := [0#u8,0#u8,0#u8,0#u8]
theorem length : bytes.length=4 := by simp only [bytes,List.length_cons,List.length_nil]

theorem selected : (NFY_JFx_NativeBytes.publicInput.val.drop 1812).take 4=bytes := by
  change (NFY_JFx_DataPublic00.bytes.drop 1812).take 4=bytes
  simp only [NFY_JFx_DataPublic00.bytes,NFY_JFx_DataPublic00.c00_length,NFY_JFx_DataPublic00.c01_length,NFY_JFx_DataPublic00.c02_length,NFY_JFx_DataPublic00.c03_length,NFY_JFx_DataPublic00.c04_length,NFY_JFx_DataPublic00.c05_length,NFY_JFx_DataPublic00.c06_length,NFY_JFx_DataPublic00.c07_length,NFY_JFx_DataPublic00.c08_length,NFY_JFx_DataPublic00.c09_length,NFY_JFx_DataPublic00.c10_length,NFY_JFx_DataPublic00.c11_length,NFY_JFx_DataPublic00.c12_length,NFY_JFx_DataPublic00.c13_length,NFY_JFx_DataPublic00.c14_length,NFY_JFx_DataPublic00.c15_length,NFY_JFx_DataPublic00.c16_length,NFY_JFx_DataPublic00.c17_length,NFY_JFx_DataPublic00.c18_length,NFY_JFx_DataPublic00.c19_length,NFY_JFx_DataPublic00.c20_length,NFY_JFx_DataPublic00.c21_length,NFY_JFx_DataPublic00.c22_length,NFY_JFx_DataPublic00.c23_length,NFY_JFx_DataPublic00.c24_length,NFY_JFx_DataPublic00.c25_length,NFY_JFx_DataPublic00.c26_length,NFY_JFx_DataPublic00.c27_length,NFY_JFx_DataPublic00.c28_length,NFY_JFx_DataPublic00.c29_length,NFY_JFx_DataPublic00.c30_length,NFY_JFx_DataPublic00.c31_length,NFY_JFx_DataPublic00.c32_length,NFY_JFx_DataPublic00.c33_length,NFY_JFx_DataPublic00.c34_length,NFY_JFx_DataPublic00.c35_length,NFY_JFx_DataPublic00.c36_length,NFY_JFx_DataPublic00.c37_length,NFY_JFx_DataPublic00.c38_length,NFY_JFx_DataPublic00.c39_length,NFY_JFx_DataPublic00.c40_length,NFY_JFx_DataPublic00.c41_length,NFY_JFx_DataPublic00.c42_length,NFY_JFx_DataPublic00.c43_length,NFY_JFx_DataPublic00.c44_length,NFY_JFx_DataPublic00.c45_length,NFY_JFx_DataPublic00.c46_length,NFY_JFx_DataPublic00.c47_length,NFY_JFx_DataPublic00.c48_length,NFY_JFx_DataPublic00.c49_length,NFY_JFx_DataPublic00.c50_length,NFY_JFx_DataPublic00.c51_length,NFY_JFx_DataPublic00.c52_length,NFY_JFx_DataPublic00.c53_length,NFY_JFx_DataPublic00.c54_length,NFY_JFx_DataPublic00.c55_length,NFY_JFx_DataPublic00.c56_length,NFY_JFx_DataPublic00.c57_length,NFY_JFx_DataPublic00.c58_length,List.drop_append,List.take_append,List.length_append,Nat.reduceAdd,Nat.reduceSub,Nat.reduceLeDiff,List.length_drop,List.drop_eq_nil_of_le,List.take_of_length_le,List.drop_zero,List.take_zero,List.nil_append,List.append_nil]
  rfl

theorem source : core.slice.index.Slice.index (core.slice.index.SliceIndexRangeUsizeSlice U8)
    NFY_JFx_NativeBytes.publicInput {start:=1812#usize,«end»:=1816#usize}=
    ok (NFY_JFu_PublicRange.segment 1812 4 (by decide)) :=
  by
    have call:=NFY_JFu_PublicRange.read 1812#usize 1816#usize (by decide) (by decide)
    simpa only [show (1812#usize).val=1812 from rfl,
      show (1816#usize).val=1816 from rfl,Nat.reduceSub] using call

#print axioms length
#print axioms selected
#print axioms source
end AspisR1.NFY_JFu_PublicMeta08
-- END copied JFu_PublicMeta08
-- BEGIN copied JFs_PaymentReads: lean/JFs_PaymentReads.lean
set_option autoImplicit false
namespace AspisR1.NFY_JFs_PaymentReads
open Aeneas Aeneas.Std Result
open AspisR1TerminalDecoder

theorem cast4 : core.array.TryFromArrayCopySlice.try_from 32#usize core.marker.CopyU8
    (NFY_JFu_PublicRange.segment 1672 32 (by decide))=ok (.Ok NFY_JFs_Cell04.value) :=
  by
  apply NFY_JFt_ExactArray.cast
  dsimp only [NFY_JFu_PublicRange.segment,NFY_JFs_Cell04.value]
  exact NFY_JFs_Cell04.selected

theorem cast5 : core.array.TryFromArrayCopySlice.try_from 32#usize core.marker.CopyU8
    (NFY_JFu_PublicRange.segment 1704 32 (by decide))=ok (.Ok NFY_JFs_Cell05.value) :=
  by
  apply NFY_JFt_ExactArray.cast
  dsimp only [NFY_JFu_PublicRange.segment,NFY_JFs_Cell05.value]
  exact NFY_JFs_Cell05.selected

theorem cast6 : core.array.TryFromArrayCopySlice.try_from 8#usize core.marker.CopyU8
    (NFY_JFu_PublicRange.segment 1736 8 (by decide))=ok (.Ok NFY_JFs_Cell06.value) :=
  by
  apply NFY_JFt_ExactArray.cast
  dsimp only [NFY_JFu_PublicRange.segment,NFY_JFs_Cell06.value]
  exact NFY_JFs_Cell06.selected

theorem cast7 : core.array.TryFromArrayCopySlice.try_from 4#usize core.marker.CopyU8
    (NFY_JFu_PublicRange.segment 1808 4 (by decide))=ok (.Ok NFY_JFs_Cell07.value) :=
  by
  apply NFY_JFt_ExactArray.cast
  dsimp only [NFY_JFu_PublicRange.segment,NFY_JFs_Cell07.value]
  exact NFY_JFs_Cell07.selected

def fee : Slice U8 := ⟨NFY_JFu_PublicMeta08.bytes,by simp [NFY_JFu_PublicMeta08.bytes];scalar_tac⟩
theorem fee_selected : NFY_JFu_PublicRange.segment 1812 4 (by decide)=fee := by
  apply Subtype.ext
  dsimp only [NFY_JFu_PublicRange.segment,fee]
  exact NFY_JFu_PublicMeta08.selected

theorem fee_bytes : core.num.U32.to_le_bytes 0#u32=
    (⟨NFY_JFu_PublicMeta08.bytes,by simp [NFY_JFu_PublicMeta08.bytes]⟩ : Array U8 4#usize) := by
  apply Subtype.ext
  simpa only [NFY_JFu_PublicMeta08.bytes,List.replicate] using AspisS6ZeroWord.u32_zero

theorem fee_compare : core.cmp.PartialEq.ne.trait_default
    (Slice.Insts.CoreCmpPartialEqSlice core.cmp.PartialEqU8) fee fee=ok false := by rfl

#print axioms cast4
#print axioms cast5
#print axioms cast6
#print axioms cast7
#print axioms fee_selected
#print axioms fee_bytes
#print axioms fee_compare
end AspisR1.NFY_JFs_PaymentReads
-- END copied JFs_PaymentReads
-- BEGIN copied JFs_PaymentCommon: lean/JFs_PaymentCommon.lean
set_option autoImplicit false
namespace AspisR1.NFY_JFs_PaymentCommon
open Aeneas Aeneas.Std Result
open AspisR1TerminalDecoder pool_v1.payment_relation

theorem source : decode_common NFY_JFs_PaymentArray.value=ok (.Ok NFY_JFs_PaymentValue.common) := by
  have validated:=NFY_JFs_PaymentValue.common_validated
  unfold NFY_JFs_PaymentValue.common at validated
  simp only [NFY_JFs_PaymentValue.asset] at validated
  have assetBound : ¬77#u32 >= aspis_core.field.P := by
    unfold aspis_core.field.P
    scalar_tac
  unfold decode_common
  simp only [ASSET_ID_OFFSET,AMOUNT_OR_RESERVED_OFFSET,POOL_OFFSET,DEPLOYMENT_DOMAIN_OFFSET,
    ANCHOR_SEQUENCE_OFFSET,ANCHOR_ROOT_OFFSET,NULLIFIER_OFFSET]
  simp only [
    NFY_JFs_PaymentArray.range 144#usize 148#usize (by decide) (by decide),
    NFY_JFs_PaymentArray.range 8#usize 40#usize (by decide) (by decide),
    NFY_JFs_PaymentArray.range 40#usize 72#usize (by decide) (by decide),
    NFY_JFs_PaymentArray.range 72#usize 80#usize (by decide) (by decide),
    NFY_JFs_PaymentArray.range 80#usize 112#usize (by decide) (by decide),
    NFY_JFs_PaymentArray.range 112#usize 144#usize (by decide) (by decide),
    show (8#usize).val=8 from rfl,
    show (40#usize).val=40 from rfl,
    show (72#usize).val=72 from rfl,
    show (80#usize).val=80 from rfl,
    show (112#usize).val=112 from rfl,
    show (144#usize).val=144 from rfl,
    show (148#usize).val=148 from rfl,
    Nat.reduceAdd,Nat.reduceSub,
    NFY_JFs_PaymentReads.cast4,NFY_JFs_PaymentReads.cast5,NFY_JFs_PaymentReads.cast6,NFY_JFs_PaymentReads.cast7,
    NFY_JFs_PaymentDigests.shared43,NFY_JFs_PaymentDigests.shared44,
    NFY_JFs_PaymentDigests.decode43,NFY_JFs_PaymentDigests.decode44,
    atomic_statement.unwrap_fixed_slice,lift,bind_tc_ok,
    NFY_JFs_PaymentValue.asset,assetBound,
    Bool.false_eq_true,↓reduceIte,
    core.result.Result.map_err,core.result.Result.Insts.CoreOpsTry.branch]
  simp only [validated,bind_tc_ok,
    core.result.Result.Insts.CoreOpsTry.branch]
  rfl

#print axioms source
end AspisR1.NFY_JFs_PaymentCommon
-- END copied JFs_PaymentCommon
-- BEGIN copied JFs_ArrayHeader: lean/JFs_ArrayHeader.lean
set_option autoImplicit false
namespace AspisR1.NFY_JFs_ArrayHeader
open Aeneas Aeneas.Std Result

theorem firstn (off : Nat) (n : Usize) (bound : off+n.val≤1880) (count : Usize)
    (inside : count.val≤n.val) :
    core.array.Array.index
      (core.ops.index.IndexSlice (core.slice.index.SliceIndexRangeToUsizeSlice U8))
      (NFY_JFs_ArrayWindow.array off n bound) {«end»:=count}=
      ok (NFY_JFu_PublicRange.segment off count.val (by omega)) := by
  unfold core.array.Array.index core.ops.index.IndexSlice NFY_JFs_ArrayWindow.array
  exact NFY_JFt_LocalWindow.firstn off n.val count bound inside

theorem index (off : Nat) (n : Usize) (bound : off+n.val≤1880) (i : Usize) :
    Array.index_usize (NFY_JFs_ArrayWindow.array off n bound) i=
    Slice.index_usize (NFY_JFu_PublicRange.segment off n.val bound) i := by rfl

#print axioms firstn
#print axioms index
end AspisR1.NFY_JFs_ArrayHeader
-- END copied JFs_ArrayHeader
-- BEGIN copied JFs_PaymentHeader: lean/JFs_PaymentHeader.lean
set_option autoImplicit false
namespace AspisR1.NFY_JFs_PaymentHeader
open Aeneas Aeneas.Std Result
open AspisR1TerminalDecoder pool_v1.payment_relation

def magic : Slice U8 := ⟨NFY_JFu_PublicMeta07.bytes.take 4,by simp [NFY_JFu_PublicMeta07.bytes];scalar_tac⟩
theorem selected : NFY_JFu_PublicRange.segment 1664 4 (by decide)=magic := by
  apply Subtype.ext
  exact NFY_JFt_LocalWindow.selected 1664 8 0 4 (by decide) (by decide) _ NFY_JFu_PublicMeta07.selected

theorem magic_call : core.array.Array.index
    (core.ops.index.IndexSlice (core.slice.index.SliceIndexRangeToUsizeSlice U8))
    NFY_JFs_PaymentArray.value {«end»:=4#usize}=ok magic := by
  simp only [NFY_JFs_PaymentArray.value,
    NFY_JFs_ArrayHeader.firstn 1664 216#usize (by decide) 4#usize (by decide),
    show (4#usize).val=4 from rfl,selected]

theorem b4 : Array.index_usize NFY_JFs_PaymentArray.value 4#usize=ok 1#u8 := by
  have h:=NFY_JFs_IndexWindow.source 1664 216 8 (by decide) 4#usize (by decide) (by decide)
    1#u8 NFY_JFu_PublicMeta07.bytes NFY_JFu_PublicMeta07.selected (by rfl)
  simpa only [NFY_JFs_PaymentArray.value,NFY_JFs_ArrayHeader.index,
    show (216#usize).val=216 from rfl] using h

theorem b5 : Array.index_usize NFY_JFs_PaymentArray.value 5#usize=ok 1#u8 := by
  have h:=NFY_JFs_IndexWindow.source 1664 216 8 (by decide) 5#usize (by decide) (by decide)
    1#u8 NFY_JFu_PublicMeta07.bytes NFY_JFu_PublicMeta07.selected (by rfl)
  simpa only [NFY_JFs_PaymentArray.value,NFY_JFs_ArrayHeader.index,
    show (216#usize).val=216 from rfl] using h

theorem b6 : Array.index_usize NFY_JFs_PaymentArray.value 6#usize=ok 1#u8 := by
  have h:=NFY_JFs_IndexWindow.source 1664 216 8 (by decide) 6#usize (by decide) (by decide)
    1#u8 NFY_JFu_PublicMeta07.bytes NFY_JFu_PublicMeta07.selected (by rfl)
  simpa only [NFY_JFs_PaymentArray.value,NFY_JFs_ArrayHeader.index,
    show (216#usize).val=216 from rfl] using h

theorem b7 : Array.index_usize NFY_JFs_PaymentArray.value 7#usize=ok 0#u8 := by
  have h:=NFY_JFs_IndexWindow.source 1664 216 8 (by decide) 7#usize (by decide) (by decide)
    0#u8 NFY_JFu_PublicMeta07.bytes NFY_JFu_PublicMeta07.selected (by rfl)
  simpa only [NFY_JFs_PaymentArray.value,NFY_JFs_ArrayHeader.index,
    show (216#usize).val=216 from rfl] using h

theorem source : require_header NFY_JFs_PaymentArray.value POOL_V1_PRIVATE_TRANSFER_STATEMENT_MAGIC
    pool_v1.historical_anchor.PoolV1TransitionKind.PrivateTransfer=ok (.Ok ()) := by
  unfold require_header
  simp only [magic_call,b4,b5,b6,b7,bind_tc_ok]
  unfold POOL_V1_PRIVATE_TRANSFER_STATEMENT_MAGIC POOL_V1_PAYMENT_STATEMENT_VERSION
    pool_v1.format.POOL_V1_DIGEST_ENCODING_VERSION
  rfl

#print axioms selected
#print axioms magic_call
#print axioms b4
#print axioms b5
#print axioms b6
#print axioms b7
#print axioms source
end AspisR1.NFY_JFs_PaymentHeader
-- END copied JFs_PaymentHeader
-- BEGIN copied JFs_PaymentDecode: lean/JFs_PaymentDecode.lean
set_option autoImplicit false
namespace AspisR1.NFY_JFs_PaymentDecode
open Aeneas Aeneas.Std Result
open AspisR1TerminalDecoder pool_v1.payment_relation

theorem source : decode_pool_v1_private_transfer_public_v1 NFY_JFu_PublicRange.payment=
    ok (.Ok NFY_JFs_PaymentValue.value) := by
  have validated:=NFY_JFs_PaymentValue.validated
  unfold NFY_JFs_PaymentValue.value at validated
  unfold decode_pool_v1_private_transfer_public_v1
  simp only [NFY_JFs_PaymentArray.shared,NFY_JFs_PaymentHeader.source,bind_tc_ok,
    core.result.Result.map_err,core.result.Result.Insts.CoreOpsTry.branch,
    AMOUNT_OR_RESERVED_OFFSET,FIRST_OUTPUT_OR_DESTINATION_OFFSET,SECOND_OUTPUT_OFFSET]
  simp only [NFY_JFs_PaymentArray.range 148#usize 152#usize (by decide) (by decide),
    show (148#usize).val=148 from rfl,show (152#usize).val=152 from rfl,
    Nat.reduceAdd,Nat.reduceSub,NFY_JFs_PaymentReads.fee_selected,
    POOL_V1_CANONICAL_FEE,NFY_JFs_PaymentReads.fee_bytes,lift,bind_tc_ok]
  have fee_slice : core.array.Array.index
      (core.ops.index.IndexSlice (core.slice.index.SliceIndexRangeUsizeSlice U8))
      (⟨NFY_JFu_PublicMeta08.bytes,by simp [NFY_JFu_PublicMeta08.bytes]⟩ : Array U8 4#usize)
      {start:=0#usize,«end»:=4#usize}=ok NFY_JFs_PaymentReads.fee := by rfl
  simp only [fee_slice,NFY_JFs_PaymentReads.fee_compare,bind_tc_ok,Bool.false_eq_true,↓reduceIte,
    NFY_JFs_PaymentCommon.source,core.result.Result.Insts.CoreOpsTry.branch]
  simp only [NFY_JFs_PaymentArray.range 152#usize 184#usize (by decide) (by decide),
    NFY_JFs_PaymentArray.suffix 184#usize (by decide),
    show (152#usize).val=152 from rfl,show (184#usize).val=184 from rfl,
    Nat.reduceAdd,Nat.reduceSub,NFY_JFs_PaymentDigests.shared45,NFY_JFs_PaymentDigests.shared46,
    atomic_statement.unwrap_fixed_slice,NFY_JFs_PaymentDigests.decode45,NFY_JFs_PaymentDigests.decode46,
    bind_tc_ok,core.result.Result.map_err,core.result.Result.Insts.CoreOpsTry.branch,validated]
  rfl

#print axioms source
end AspisR1.NFY_JFs_PaymentDecode
-- END copied JFs_PaymentDecode
-- BEGIN copied JFs_PublicEncoders: lean/JFs_PublicEncoders.lean
set_option autoImplicit false
namespace AspisR1.NFY_JFs_PublicEncoders
open Aeneas Aeneas.Std Result
open AspisR1TerminalDecoder

theorem payment : ∃ encoded : Array U8 216#usize, encoded.val=NFY_JFu_PublicRange.payment.val ∧
    pool_v1.payment_relation.encode_pool_v1_private_transfer_public_v1 NFY_JFs_PaymentValue.value=
      ok (.Ok encoded) :=
  AspisS6NativePaymentContents.transfer_accepted_inverse _ _ NFY_JFs_PaymentDecode.source

theorem late : ∃ updated : Slice U8,
    pool_v1.pair_tree_profile.encode_pool_v1_pair_late_public_statement_v1 NFY_JFs_LateChildren.value
      (Array.to_slice (Array.repeat 1520#usize 0#u8))=ok (.Ok (),updated) ∧ updated.length=1520 := by
  apply AspisS6NativeLateEncodeAccepted.encode_from_decode _ _ NFY_JFs_LateDecode.source
  simp only [Array.to_slice,Array.repeat,Slice.length,List.length_replicate]
  rfl

#print axioms payment
#print axioms late
end AspisR1.NFY_JFs_PublicEncoders
-- END copied JFs_PublicEncoders

run_cmd do
 let env ← Lean.getEnv
 env.constants.toList.forM fun (n, ci) => do
  if ci.isTheorem && (env.getModuleIdxFor? n).isNone then
   Lean.Elab.Command.elabCommand (← `(command| #print axioms $(Lean.mkIdent n)))
