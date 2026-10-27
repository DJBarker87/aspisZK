import XRm_CompactShape
open Aeneas Aeneas.Std Result
open XRk_Release
namespace XRm_CompactLength
/-- Total source rejection at the first guard, before any array/range read. -/
theorem reject (proof : Slice U8) (size : Usize)
    (constant : compact.PROOF_BYTES=ok size) (wrong : Slice.len proof≠size) :
    verifier.candidate.parse_shape proof=ok (.Err .Parse) := by
  unfold verifier.candidate.parse_shape
  rw [constant,bind_tc_ok]
  have test : (Slice.len proof != size)=true := by simpa only [bne_iff_ne] using wrong
  rw [if_pos test]
#print axioms reject
end XRm_CompactLength
