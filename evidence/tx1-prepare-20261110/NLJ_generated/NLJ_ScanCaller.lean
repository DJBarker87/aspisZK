import NKL_ScanRoot
import NJS_Parse
set_option autoImplicit false
noncomputable section
namespace AspisR1.NLJ_ScanCaller
open Aeneas Aeneas.Std Result AspisR1
open NKL_Checks NKL_ScanAtoms NKL_NativeGuard NKL_ScanSequence
/-- The preceding successful parser establishes the scanner's full-length
carrier domain on the SAME proof. This is a local reached-call theorem. -/
theorem domain (proof : Slice U8) (variant : Op3I_Source.transport.Variant)
 (parsed : Op3I_Source.verifier.candidate.parse_shape Op3I_Std.ops proof = ok (.Ok variant)) :
 proof.val.length = 57607 := (Op3I_ParseLaws.source_success proof variant parsed).2.1

def original (proof : Slice U8) (length : proof.val.length = 57607) : Array U8 57607#usize :=
 ⟨proof.val,by simpa only [UScalar.ofNatCore_val_eq] using length⟩
theorem same_original (proof : Slice U8) (length : proof.val.length = 57607) :
 (original proof length).to_slice = proof := rfl
/-- Install CLOSED084 at that original proof, without choosing another buffer.
The physical scan cut is the exact reviewed NKL predicate, not a free Result.
The preceding parser observation is discharged by the parent's parse step
before any native row root may use this local domain lemma. -/
theorem installed (proof : Slice U8) (variant : Op3I_Source.transport.Variant)
 (parsed : Op3I_Source.verifier.candidate.parse_shape Op3I_Std.ops proof = ok (.Ok variant))
 (out : Reply) (events : List Check) (after : Bytes)
 (native : Invoke (checks proof) out events proof.val after) :
 ok out = (do let valid ← MultiproofParserRef.parser_reference.scan proof
              ok (NKB_CanonicalOpening.reply valid)) ∧ after = proof.val := by
 let p := original proof (domain proof variant parsed)
 have same : p.to_slice = proof := rfl
 have pval : p.val = proof.val := rfl
 have cut : Invoke (checks p.to_slice) out events p.val after := by simpa only [same,pval] using native
 exact ⟨by simpa only [same] using NKL_ScanRoot.adopted p out events after cut,
  (NKL_ScanRoot.deployed p out events after cut).2.1.trans pval⟩
#print axioms domain
#print axioms same_original
#print axioms installed
#print installed
end AspisR1.NLJ_ScanCaller
end
