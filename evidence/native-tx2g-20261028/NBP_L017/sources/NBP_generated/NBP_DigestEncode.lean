import S2K_DigestBytes
import NBG_WideBytes
set_option autoImplicit false
noncomputable section
namespace NBP_DigestEncode
open Aeneas Aeneas.Std Result AspisR1TerminalDecoder
open AspisR1.S2K
/-- Exact full encoder, all raw limbs; reuses the existing decreasing-loop
induction on the selected cohort rather than re-proving it. -/
theorem result (digest : Array U32 8#usize) :
    atomic_statement.encode_digest_canonical digest = ok (DigestBytes.bytes digest) :=
  DigestBytes.exact digest
/-- The same arbitrary pre-state update checked by native NBG_K020. -/
theorem step (digest : Array U32 8#usize) (index : Usize)
    (range : index.val < 8) (output : Array U8 32#usize) :
    atomic_statement.encode_digest_canonical_loop.body (DigestTotal.cursor digest index) output =
      ok (.cont
        (DigestTotal.cursor digest (Usize.ofNatCore (index.val+1) (by scalar_tac)),
         output.setSlice! (4*index.val)
           (core.num.U32.to_le_bytes
             (digest.val[index.val]'(by have := digest.property; change digest.val.length=8 at this; omega))).val)) :=
  DigestTotal.body_word digest index range output
#print axioms result
#print axioms step
#print axioms DigestBytes.loop_exact
#print axioms DigestTotal.next_row
#print axioms DigestTotal.exhausted
end NBP_DigestEncode
