import NCM_KeyView
import NCM_Leaf

set_option autoImplicit false
noncomputable section
namespace AspisR1.NCM_ViewAddress
open Aeneas Aeneas.Std Result NCE_OpeningCuts
open AspisV8R19.SqueezeOracleBridge

/-- Exact slices supplied to the leaf syscall, from the SAME checked source
range and proof carrier. The digest value remains the runtime interpretation. -/
theorem address (s : Carrier) (size : s.proof.val.length = 57607)
    (parsed : OraclePortCompactDraft.Parsed)
    (wire : parsed.wire = MultiproofConeCanonical.bytesOf s.proof.val)
    (i kind : Usize) (bound : i.val < 22) (view : Slice U8)
    (source : Port4B_Opening.opening s.proof i = ok view) :
    flatten (Port4B_LeafCode.input kind view) = OraclePortSelectedDraft.leaf parsed kind.val i.val := by
  obtain ⟨expected,read,len,bytes⟩ := Port4B_Opening.opening_exact s.proof size i bound
  have same := Result.ok.inj (source.symm.trans read)
  subst expected
  rw [Port4B_LeafCode.address]
  have opened : MultiproofConeCanonical.bytesOf view.val = OraclePortSelectedDraft.opening parsed i.val := by
    simpa only [OraclePortSelectedDraft.opening,wire] using bytes
  rw [opened]
  exact MultiproofConeOpeningAdapters.leaf_address parsed kind.val i.val

#print axioms address
end AspisR1.NCM_ViewAddress
end
