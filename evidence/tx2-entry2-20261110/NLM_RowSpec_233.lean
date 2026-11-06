import NLM_Auth233
import NLM_PacketTypes
set_option autoImplicit false
noncomputable section
namespace NLM_RowSpec_233
open Aeneas Aeneas.Std Result AdapterRw NLM_Auth233 NLM_PacketTypes
abbrev Native (Ambient : Type) := Key → Slice Owned → Key → U8 → U64 →
 World Ambient → Observation Ambient Event (core.result.Result Auth PE)
/-- Draft per-invocation interface for OPEN TX2:233. No success
premise, chosen child Result, endpoint-only projection or independent effect
list. All nominal arguments and every fail/div prefix are in the source Run.
Ops is the fixed source installation to be supplied by the child's owner;
this intermediate specification is NOT a positive native row root. -/
def RowSpec_233 {Ambient : Type} (ops : Ops) (native : Native Ambient) : Prop :=
 ∀ program accounts pool lane slot world,
 native program accounts pool lane slot world =
 ⟨world,G ops program accounts pool lane slot⟩ ∧
 (native program accounts pool lane slot world).run.result =
 r1_pool_adapter.owned.authenticate_asq8_accounts ops program accounts pool lane slot
#print RowSpec_233
end NLM_RowSpec_233
