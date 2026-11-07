import LIB_VParsePrefix
import ExtractedPrefixParse
set_option autoImplicit false
noncomputable section
namespace AspisR1.NNG_PrefixRoot094
open Aeneas Aeneas.Std Result
/-- The CLOSED parser's SAME original slice supplies C1, including the
complete32-byte copy. No whole parser normalization is performed. -/
theorem root (source : Slice U8) (p : LIB_VCarriers.Prefix)
 (returned : LIB_VParsePrefix.model (LIB_Carriers.bytes source)=ok (.ok p)) :
 p.parsed.c1_root.val=source.val.take 32 := by
 rw [LIB_VParsePrefix.model_same] at returned
 unfold LIB_VParsePrefix.parseRaw at returned
 split at returned
 · have equal := Except.ok.inj (Result.ok.inj returned)
   have sourceEq : p.source=source := congrArg LIB_VCarriers.Prefix.source equal.symm
   have facts := (ExtractedPrefixParse.parse_success p.source p.parsed p.parse_eq).1
   rw [sourceEq] at facts
   exact facts
 · cases returned
 · cases returned
 · cases returned

#print axioms root
end AspisR1.NNG_PrefixRoot094
