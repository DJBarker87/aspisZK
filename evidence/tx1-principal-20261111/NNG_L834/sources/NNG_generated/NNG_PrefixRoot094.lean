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
 cases parsed : AspisR1PrefixAggregateParser.r1_wire.Prefix.parse source with
 | fail e=>simp only [LIB_VParsePrefix.parseRaw,parsed] at returned;cases returned
 | div=>simp only [LIB_VParsePrefix.parseRaw,parsed] at returned;cases returned
 | ok reply=>
   cases reply with
   | Err e=>simp only [LIB_VParsePrefix.parseRaw,parsed] at returned;cases returned
   | Ok raw=>
     simp only [LIB_VParsePrefix.parseRaw,parsed] at returned
     have same : p=⟨source,raw,parsed⟩ := (Except.ok.inj (Result.ok.inj returned)).symm
     rw [same]
     exact (ExtractedPrefixParse.parse_success source raw parsed).1
#print axioms root
end AspisR1.NNG_PrefixRoot094
