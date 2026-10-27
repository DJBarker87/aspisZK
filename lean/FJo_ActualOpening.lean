import FJl_OpeningBytes
set_option autoImplicit false
noncomputable section
namespace AspisR1.FJo_ActualOpening
open Aeneas Aeneas.Std Result MultiproofConeCanonical
open OraclePortCompactDraft OraclePortSelectedDraft
/-- Both literal bytes and width of the SAME reached opening operand. -/
theorem value (proof : Slice U8) (size : proof.val.length=57607) (parsed : Parsed)
    (wire : parsed.wire=bytesOf proof.val) (i : Usize) (bound : i.val<22) (selected : Slice U8)
    (run : Port4B_Opening.opening proof i=ok selected) :
    bytesOf selected.val=opening parsed i.val ∧ selected.val.length=832 := by
  obtain ⟨v,call,len,bytes⟩ := Port4B_Opening.opening_exact proof size i bound
  have same := Result.ok.inj (run.symm.trans call)
  subst v
  constructor
  · rwa [←wire] at bytes
  · exact len
#print axioms value
end AspisR1.FJo_ActualOpening
end
