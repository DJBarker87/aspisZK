import NDO_JFt_Digest43
import NDO_JFt_Digest44
import NDO_JFt_Digest45
import NDO_JFt_Digest46
import NDO_JFt_DigestArray
set_option autoImplicit false
namespace AspisR1.JFs_PaymentDigests
open Aeneas Aeneas.Std Result
open AspisR1TerminalDecoder

def bytes43 : Array U8 32#usize := ⟨JFu_PublicDigest43.bytes,JFu_PublicDigest43.length⟩
theorem selected43 : (JFu_PublicRange.segment 1744 32 (by decide)).val=bytes43.val := by
  dsimp only [JFu_PublicRange.segment,bytes43]
  exact JFu_PublicDigest43.selected
theorem shared43 : core.array.TryFromSharedArraySlice.try_from 32#usize
    (JFu_PublicRange.segment 1744 32 (by decide))=ok (.Ok bytes43) :=
  JFt_DigestArray.shared _ _ selected43
theorem decode43 : atomic_statement.decode_digest_canonical bytes43=ok (.Ok JFt_Digest43.value) :=
  JFt_DigestArray.source _ _ selected43 _ JFt_Digest43.source

def bytes44 : Array U8 32#usize := ⟨JFu_PublicDigest44.bytes,JFu_PublicDigest44.length⟩
theorem selected44 : (JFu_PublicRange.segment 1776 32 (by decide)).val=bytes44.val := by
  dsimp only [JFu_PublicRange.segment,bytes44]
  exact JFu_PublicDigest44.selected
theorem shared44 : core.array.TryFromSharedArraySlice.try_from 32#usize
    (JFu_PublicRange.segment 1776 32 (by decide))=ok (.Ok bytes44) :=
  JFt_DigestArray.shared _ _ selected44
theorem decode44 : atomic_statement.decode_digest_canonical bytes44=ok (.Ok JFt_Digest44.value) :=
  JFt_DigestArray.source _ _ selected44 _ JFt_Digest44.source

def bytes45 : Array U8 32#usize := ⟨JFu_PublicDigest45.bytes,JFu_PublicDigest45.length⟩
theorem selected45 : (JFu_PublicRange.segment 1816 32 (by decide)).val=bytes45.val := by
  dsimp only [JFu_PublicRange.segment,bytes45]
  exact JFu_PublicDigest45.selected
theorem shared45 : core.array.TryFromSharedArraySlice.try_from 32#usize
    (JFu_PublicRange.segment 1816 32 (by decide))=ok (.Ok bytes45) :=
  JFt_DigestArray.shared _ _ selected45
theorem decode45 : atomic_statement.decode_digest_canonical bytes45=ok (.Ok JFt_Digest45.value) :=
  JFt_DigestArray.source _ _ selected45 _ JFt_Digest45.source

def bytes46 : Array U8 32#usize := ⟨JFu_PublicDigest46.bytes,JFu_PublicDigest46.length⟩
theorem selected46 : (JFu_PublicRange.segment 1848 32 (by decide)).val=bytes46.val := by
  dsimp only [JFu_PublicRange.segment,bytes46]
  exact JFu_PublicDigest46.selected
theorem shared46 : core.array.TryFromSharedArraySlice.try_from 32#usize
    (JFu_PublicRange.segment 1848 32 (by decide))=ok (.Ok bytes46) :=
  JFt_DigestArray.shared _ _ selected46
theorem decode46 : atomic_statement.decode_digest_canonical bytes46=ok (.Ok JFt_Digest46.value) :=
  JFt_DigestArray.source _ _ selected46 _ JFt_Digest46.source

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
end AspisR1.JFs_PaymentDigests
