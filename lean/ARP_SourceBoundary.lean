import AdapterRwAccepted
set_option autoImplicit false
namespace AspisR1.ARP_SourceBoundary
open Aeneas Aeneas.Std Result

/-- A tiny rejected input separates a constantly-successful fixture native
from the actual source for EVERY dictionary. No crypto computation is needed. -/
theorem empty_accounts_reject (ops : AdapterRw.Ops)
    (id : AdapterRw.solana_pubkey.Pubkey) (data : Slice U8)
    (saved : alloc.vec.Vec U8) :
    AdapterRw.r1_pool_adapter.owned.stage1_owned ops id (⟨[],by simp⟩) data ≠
      ok (.Ok saved) := by
  intro success
  obtain ⟨pa,pu,pub,raw,statement,semantic,selected,split,firstIndex,rest⟩ :=
    AdapterRw.Accepted.first_call ops id (⟨[],by simp⟩) data saved success
  simp [Slice.index_usize] at firstIndex

#print axioms empty_accounts_reject
end AspisR1.ARP_SourceBoundary
