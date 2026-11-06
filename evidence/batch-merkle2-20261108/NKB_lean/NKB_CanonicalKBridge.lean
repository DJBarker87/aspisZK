import NKB_CanonicalCuts
import NJC_ReaderResults
set_option autoImplicit false
noncomputable section
namespace NKB_CanonicalKBridge
open Aeneas Aeneas.Std Result AspisR1 NKB_CanonicalRange NKB_CanonicalOpening
open OraclePortCkptAbi4Decode CheckpointBytes3KDecode CheckpointBytes3ScalarShape
attribute [local instance] Classical.propDecidable

def good (b : Array U8 16#usize) : Bool := decide (Canonical
 (kWords (word b.to_slice b.property 0) (word b.to_slice b.property 1)
   (word b.to_slice b.property 2) (word b.to_slice b.property 3)))

def caller : core.result.Result AspisR1Stage2.aspis_core.field.QM31
 AspisR1Stage2.verifier.Error→ScanResult
 | .Ok _=>.Ok () | .Err _=>.Err .Parse

theorem natural (b : Array U8 16#usize) :
 caller (NJC_ReaderResults.naturalK b)=reply (good b) := by
 unfold NJC_ReaderResults.naturalK caller good reply
 split_ifs <;> simp_all

/-- The CLOSED actual K decoder is substituted on the SAME16 bytes. Both
Option branches retain exactly the caller's Unit Result; no canonical-input
or child-success hypothesis is introduced. The four-word native guard-byte
association and the complete adopted scanner equation remain separate. -/
theorem source (b : Array U8 16#usize) :
 (do let parsed←OraclePortCkptAbi2Extracted.decode_k_spec b.to_slice
     ok (if parsed.isSome then (.Ok () : ScanResult) else .Err .Parse))=
 ok (reply (good b)) := by
 have decode:=NJC_ReaderResults.decodeK b
 cases h:OraclePortCkptAbi2Extracted.decode_k_spec b.to_slice with
 | fail error=>simp only [h,bind_tc_fail] at decode;cases decode
 | div=>simp only [h,bind_tc_div] at decode;cases decode
 | ok parsed=>
   simp only [h,bind_tc_ok] at decode
   have eq:=congrArg caller (Result.ok.inj decode)
   rw [natural] at eq
   simp only [h,bind_tc_ok]
   cases parsed <;> simpa only [CheckpointBytes3Reader.optionK,caller,
     Option.isSome_none,Option.isSome_some,Bool.false_eq_true,if_false,if_true] using congrArg Result.ok eq

#print axioms natural
#print axioms source
end NKB_CanonicalKBridge
