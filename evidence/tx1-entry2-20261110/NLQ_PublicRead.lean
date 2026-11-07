import NLQ_SnapshotData
set_option autoImplicit false
noncomputable section
namespace NLQ_PublicRead
open Aeneas Aeneas.Std Result AspisR1 AspisR1.S2W_D189Entry
/-- The decoder's buffer is the original public account's1880 bytes. This
caller clause is derived at the read occurrence; there is no root read-success
premise and no independently chosen public byte allocation. -/
theorem at_site (e : Entry) (ops : AdapterRw.Ops) (bytes : Slice U8)
 (read : AdapterRw.r1_pool_adapter.owned.OwnedAccount.data ops (e.snapshot 1 1880 1880)=.ok (.Ok bytes)) :
 bytes=e.buffers (e.handles 1).1 ∧ bytes.val.length=1880 := by
 obtain ⟨same,h⟩ := NLQ_SnapshotData.returned e ops 1 1880 1880 bytes read
 refine ⟨same,?_⟩
 rw [same]
 exact h.elim id id
#check @at_site
#print axioms at_site
end NLQ_PublicRead
