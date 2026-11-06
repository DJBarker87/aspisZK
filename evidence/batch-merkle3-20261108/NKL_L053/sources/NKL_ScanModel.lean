import NKL_ScanRows
import NKL_PrefixCanonical
import NKL_Checks
import MultiproofConeStrictScan
set_option autoImplicit false
noncomputable section
namespace NKL_ScanModel
open Aeneas Aeneas.Std Result AspisR1
open OraclePortCompactDraft MultiproofConeCanonical
attribute [local instance] Classical.propDecidable

theorem predicate (proof : Slice U8) (width:proof.val.length=57607) :
 (NKL_Checks.checks proof).all NKL_Checks.test=true ↔ scan (bytesOf proof.val) := by
 rw [NKL_Checks.source,Bool.and_eq_true,NKL_PrefixCanonical.source proof width,NKL_ScanRows.source proof width]
 simp only [NKL_PrefixCanonical.model,scan,and_assoc]

theorem value (proof : Slice U8) (width:proof.val.length=57607) :
 (NKL_Checks.checks proof).all NKL_Checks.test=decide (scan (bytesOf proof.val)) := by
 have meaning:=predicate proof width
 cases h:(NKL_Checks.checks proof).all NKL_Checks.test <;> simp_all

/-- Full Result equation for the emitted frozen canonical scanner with
concrete CLOSED children. No native whole-parent result is assumed; this
source-to-model equation is still separate from the native invocation root. -/
theorem source (proof : Slice U8) (width:proof.val.length=57607) :
 NJS_Extract.verifier.candidate.canonical_scan
  AspisR1M31Parser.field.M31.from_le_bytes NKL_CanonicalInstallation.childK
  NKL_CanonicalInstallation.childE NKL_CanonicalInstallation.childCV proof=
 ok (NKB_CanonicalOpening.reply (decide (scan (bytesOf proof.val)))) := by
 rw [NKL_CanonicalInstallation.source proof width,←NKL_Checks.source,value proof width]

theorem adopted (proof : Slice U8) (width:proof.val.length=57607) :
 NJS_Extract.verifier.candidate.canonical_scan
  AspisR1M31Parser.field.M31.from_le_bytes NKL_CanonicalInstallation.childK
  NKL_CanonicalInstallation.childE NKL_CanonicalInstallation.childCV proof=
 (do let valid←MultiproofParserRef.parser_reference.scan proof
     ok (NKB_CanonicalOpening.reply valid)) := by
 rw [source proof width,MultiproofConeStrictScan.scan_total proof width]
 rfl

set_option pp.proofs false
#print source
#print adopted
#print axioms predicate
#print axioms value
#print axioms source
#print axioms adopted
end NKL_ScanModel
end
