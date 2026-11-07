import NMP_Canonical179
import NKL_ScanRoot
set_option autoImplicit false
noncomputable section
namespace AspisR1.NMP_CallerCanonical
open Aeneas Aeneas.Std Result
/-- Upstream caller clause only: a SAME successful CLOSED canonical_scan
invocation supplies prepare's own-byte predicate. This does not instantiate
TX1:094's native producer, and creates no new canonical_scan bridge. -/
theorem from_scan (proof : Array U8 57607#usize) (events : List NKL_Checks.Check)
 (after : NKL_ScanSequence.Bytes)
 (native : NKL_ScanSequence.Invoke (NKL_Checks.checks proof.to_slice)
  (.Ok ()) events proof.val after) :
 NMP_Canonical179.Canonical (NMP_Expansion179.compactInput proof.to_slice) := by
 have reply := (NKL_ScanSequence.exact native).1.trans
  (NKL_ScanSequence.result (NKL_Checks.checks proof.to_slice))
 have good : (NKL_Checks.checks proof.to_slice).all NKL_NativeGuard.nativeGuard=true := by
  cases h : (NKL_Checks.checks proof.to_slice).all NKL_NativeGuard.nativeGuard with
  | false => rw [h] at reply;cases reply
  | true => rfl
 have all : (NKL_Checks.checks proof.to_slice).all NKL_Checks.test=true := by
  rw [←NKL_ScanRoot.all_source _ (NKL_ScanDomains.source proof.to_slice proof.property)]
  exact good
 have member : NKL_Checks.Check.cv proof.to_slice ∈ NKL_Checks.checks proof.to_slice := by
  simp only [NKL_Checks.checks,NKL_Checks.header,List.mem_append,List.mem_cons,true_or]
 have cv := List.all_eq_true.mp all _ member
 change NKL_CanonicalChildren.compactGood (NKB_CanonicalPrefix.values proof.to_slice)=true at cv
 have same : NKB_CanonicalPrefix.values proof.to_slice=NMP_Expansion179.compactInput proof.to_slice := by
  apply Subtype.ext
  rfl
 rw [same] at cv
 unfold NKL_CanonicalChildren.compactGood at cv
 intro i hi
 exact List.all_eq_true.mp cv i (List.mem_range.mpr hi)
#print axioms from_scan
#print from_scan
end AspisR1.NMP_CallerCanonical
end
