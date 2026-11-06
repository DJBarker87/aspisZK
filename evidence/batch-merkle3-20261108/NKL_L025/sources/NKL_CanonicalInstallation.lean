import NKL_CanonicalChildren
import NKL_CanonicalKCarrier
import NKB_CanonicalScalarBridge
import NKB_CanonicalDomains
set_option autoImplicit false
noncomputable section
namespace NKL_CanonicalInstallation
open Aeneas Aeneas.Std Result AspisR1 NKB_CanonicalRange
attribute [local instance] Classical.propDecidable

def childK (bytes : Slice U8) : Result (Option K) :=
 if bytes.val.length=16 then
  NKL_CanonicalKCarrier.mapResult (Option.map NKL_CanonicalKCarrier.toCaller)
    (OraclePortCkptAbi2Extracted.decode_k_spec bytes)
 else ok none

def childE (bytes : Slice U8) (_flag : Bool) : Result ScanResult := do
 let r ← NFU_Retarget.verifier.echeck bytes false
 ok (match r with | .Ok u => .Ok u | .Err _ => .Err .Parse)

def childCV (bytes : Slice U8) : Result (core.result.Result Unit NJS_Extract.compact.CodecError) := do
 let r ← NFU_Retarget.compact.check_values bytes
 ok (match r with | .Ok u => .Ok u | .Err _ => .Err .NonCanonical)

theorem k_total (bytes : Slice U8) :
 childK bytes=ok (NKL_CanonicalKCarrier.selected bytes) := by
 unfold childK
 by_cases width:bytes.val.length=16
 · rw [if_pos width]
   exact NKL_CanonicalKCarrier.decoder bytes width
 · simp only [if_neg width,NKL_CanonicalKCarrier.selected,dif_neg width]

theorem e_total (bytes : Slice U8) (flag : Bool) :
 childE bytes flag=ok (NKB_CanonicalOpening.reply (NKL_CanonicalChildren.echeckGood bytes)) :=
 NKL_CanonicalChildren.echeck_call bytes

theorem cv_total (bytes : Slice U8) :
 childCV bytes=ok (NKB_CanonicalPrefix.codec (NKL_CanonicalChildren.compactGood bytes)) := by
 unfold childCV
 rw [NKL_CanonicalChildren.compact_result]
 cases h:NKL_CanonicalChildren.compactGood bytes <;> rfl

/-- Every K caller uses the original decoder on exactly16 bytes; the explicit
extension in childK is never selected at a reached K call. -/
theorem k_c1 (q : Slice U8) (width:q.val.length=832) (s : Usize) (slot:s.val<4) :
 childK (NKB_CanonicalTail.window q s)=
 NKL_CanonicalKCarrier.mapResult (Option.map NKL_CanonicalKCarrier.toCaller)
  (OraclePortCkptAbi2Extracted.decode_k_spec (NKB_CanonicalTail.window q s)) := by
 unfold childK
 rw [if_pos (NKB_CanonicalDomains.c1 q width s slot)]

theorem k_c2 (q : Slice U8) (width:q.val.length=832) (s l : Usize)
 (slot:s.val<4) (lane:l.val<2) :
 childK (NKB_CanonicalRange.window q s l)=
 NKL_CanonicalKCarrier.mapResult (Option.map NKL_CanonicalKCarrier.toCaller)
  (OraclePortCkptAbi2Extracted.decode_k_spec (NKB_CanonicalRange.window q s l)) := by
 unfold childK
 rw [if_pos (NKB_CanonicalDomains.c2 q width s l slot lane)]

/-- Complete emitted scanner with concrete CLOSED children at their SAME
arguments. This is a source theorem, not yet a native/adopted row root. No
arbitrary operation dictionary or successful child is a hypothesis. -/
theorem source (proof : Slice U8) (width:proof.val.length=57607) :
 NJS_Extract.verifier.candidate.canonical_scan
  AspisR1M31Parser.field.M31.from_le_bytes childK childE childCV proof =
 ok (NKB_CanonicalOpening.reply
  (NKB_CanonicalPrefix.guard NKL_CanonicalChildren.compactGood NKL_CanonicalChildren.echeckGood proof &&
   NKB_CanonicalPair.allFrom
    (NKB_CanonicalRows.pass NKB_CanonicalScalarBridge.scalar NKL_CanonicalKCarrier.selected
      NKL_CanonicalChildren.echeckGood proof) 0 22)) := by
 have k : childK=(fun bytes=>ok (NKL_CanonicalKCarrier.selected bytes)) := funext k_total
 have e : childE=(fun bytes _=>ok (NKB_CanonicalOpening.reply (NKL_CanonicalChildren.echeckGood bytes))) :=
  funext fun bytes=>funext fun flag=>e_total bytes flag
 have cv : childCV=(fun bytes=>ok (NKB_CanonicalPrefix.codec (NKL_CanonicalChildren.compactGood bytes))) := funext cv_total
 have f : AspisR1M31Parser.field.M31.from_le_bytes=(fun bytes=>ok (NKB_CanonicalScalarBridge.scalar bytes)) :=
  funext NKB_CanonicalScalarBridge.source
 rw [k,e,cv,f]
 exact NKB_CanonicalPrefix.source _ _ _ _ proof width

set_option pp.proofs false
#print source
#print axioms k_total
#print axioms e_total
#print axioms cv_total
#print axioms k_c1
#print axioms k_c2
#print axioms source
end NKL_CanonicalInstallation
end
