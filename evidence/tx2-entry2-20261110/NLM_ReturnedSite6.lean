import NLM_ReturnedReads
import NLM_SevenSites
set_option autoImplicit false
noncomputable section
namespace NLM_ReturnedSite6
open Aeneas Aeneas.Std AspisR1.S2W_D189Entry NLM_Snapshot
/-- Extent at source snapshot occurrence 6; both conditions are entered
calls, not extra premises of the deployed headline. -/
theorem extent (ops : AdapterRw.Ops) (e : Entry) (allocation : Result Unit)
 (value : NLM_Snapshot.Owned) (post : NLM_Snapshot.State) (bytes : Slice U8)
 (entered : (G (NLM_SevenSites.before e 6) 6 1768 1768 allocation).result=.ok (value,post))
 (read : AdapterRw.r1_pool_adapter.owned.OwnedAccount.data (NGL_CloneDomain.install ops)
   value=.ok (.Ok bytes)) : bytes.val.length=1768 ∨ bytes.val.length=1768 := by
 have h := (NLM_ReturnedReads.data ops e 6 6 1768 1768
  (NLM_SevenSnapshots.ownedValues e (NLM_SevenSites.sites.take 6)) allocation value post bytes entered read).1
 unfold Entry.snapshot at h
 dsimp only at h
 split at h
 · rename_i allowed
   cases h
   exact allowed
 · cases h
#print extent
#print axioms extent
end NLM_ReturnedSite6
