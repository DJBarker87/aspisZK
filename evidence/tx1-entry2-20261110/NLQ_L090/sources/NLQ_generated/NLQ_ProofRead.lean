import NLQ_SnapshotData
set_option autoImplicit false
noncomputable section
namespace NLQ_ProofRead
open Aeneas Aeneas.Std Result AspisR1 AspisR1.S2W_D189Entry
/-- Full original proof account extent before selecting the688-byte candidate
prefix and57607-byte suffix. No content is inferred from address identity. -/
theorem at_site (e : Entry) (ops : AdapterRw.Ops) (bytes : Slice U8)
 (read : AdapterRw.r1_pool_adapter.owned.OwnedAccount.data ops (e.snapshot 0 58295 58295)=.ok (.Ok bytes)) :
 bytes=e.buffers (e.handles 0).1 ∧ bytes.val.length=58295 := by
 obtain ⟨same,h⟩ := NLQ_SnapshotData.returned e ops 0 58295 58295 bytes read
 refine ⟨same,?_⟩
 rw [same]
 exact h.elim id id
#check @at_site
#print axioms at_site
end NLQ_ProofRead
