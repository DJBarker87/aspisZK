import NCM_WindowImage
import Port4B_Opening

set_option autoImplicit false
noncomputable section
namespace AspisR1.NCM_Opening
open Aeneas Aeneas.Std Result NCE_OpeningCuts

/-- The actual checked range constructs the slice witness. Its value is
identified with the SAME per-byte reader output; no successful opening or
separately selected buffer is a hypothesis. This is a value association,
not a claim that the Rust borrow allocates or copies 832 bytes. -/
theorem observation (reader : Reader) (cut : NCE_Native_Opening reader)
    (s : Carrier) (i : Usize) (size : s.proof.val.length = 57607) (bound : i.val < 22) :
    ∃ view, Port4B_Opening.opening s.proof i = ok view ∧ view.val.length = 832 ∧
      readWindow reader i.val 832 0 s = ok (view.val,s) := by
  obtain ⟨view,read,len,bytes⟩ := Port4B_Opening.opening_exact s.proof size i bound
  have viewEq : view.val = (s.proof.val.drop (10055+832*i.val)).take 832 := by
    apply MultiproofConeByteEquality.bytes_injective
    simpa only [MultiproofConeCanonical.bytesOf,OraclePortCompactDraft.slice,
      List.map_take,List.map_drop,Nat.mul_comm] using bytes
  refine ⟨view,read,len,?_⟩
  rw [NCE_OpeningCuts.opening reader cut s i.val size bound,viewEq]
  rw [NCM_WindowImage.image_slice _ _ _ (by omega)]

#print axioms observation
end AspisR1.NCM_Opening
end
