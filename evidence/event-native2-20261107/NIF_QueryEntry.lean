import NIF_ScanDomain
import NFS_QueryInvariant
set_option autoImplicit false
noncomputable section
namespace AspisR1.NIF_QueryEntry
open Aeneas Aeneas.Std Result OraclePortCompactDraft MultiproofConeCanonical
open AspisR1Stage2 Port3_NativeQueryBody
/-- Every active iteration selects an opening already checked by the scan;
canonicality does not arise from the field decoder's successful arm. -/
theorem active_opening (proof : Slice U8) (size : proof.val.length=57607)
 (scan : OraclePortCompactDraft.scan (bytesOf proof.val))
 (p : verifier.Prepared) (start finish : Nat) (a : verifier.Accumulator)
 (b : verifier.BatchedWeights) (domain : NFS_QueryInvariant.Domain p start finish a b)
 (limit : finish≤22) (active : a.next.val<finish) :
 ∃ q, Port4B_Opening.opening proof a.next=ok q ∧ q.val.length=832 ∧
 canonical (slice (bytesOf q.val) 672 128) := by
 obtain ⟨q,hq,qlen,qbytes⟩ := Port4B_Opening.opening_exact proof size a.next (by omega)
 refine ⟨q,hq,qlen,?_⟩
 rw [qbytes]
 exact NIF_ScanDomain.opening_fields proof a.next.val (by omega) scan
#print axioms active_opening
end AspisR1.NIF_QueryEntry
