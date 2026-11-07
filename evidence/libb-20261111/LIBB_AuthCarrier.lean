import LIBB_PoolCarriers
import NND_AuthCarrier
set_option autoImplicit false
noncomputable section
namespace LIBB_AuthCarrier
open Aeneas Aeneas.Std
attribute [local instance] Classical.propDecidable
abbrev Raw := AdapterRw.r1_pool_adapter.AuthenticatedAsq8Accounts
/-- Partial inverse of a carrier only; no execution or success relation. -/
def raw (a : RSL.Authenticated) : Option Raw :=
 if h : ∃ r, NND_Carrier.auth r = a then some (Classical.choose h) else none

theorem exact_carrier (a : Raw) :
 NMS_R2N_RSLPoolCarriers.authenticated a = NND_Carrier.auth a := rfl

theorem roundtrip (a : Raw) : raw (NND_Carrier.auth a) = some a := by
 unfold raw
 rw [dif_pos ⟨a,rfl⟩]
 congr 1
 exact NND_Carrier.auth_injective (Classical.choose_spec (show ∃ r, NND_Carrier.auth r = NND_Carrier.auth a from ⟨a,rfl⟩))
#print axioms exact_carrier
#print axioms roundtrip
end LIBB_AuthCarrier
end
