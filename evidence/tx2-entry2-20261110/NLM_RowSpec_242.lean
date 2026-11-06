import NLM_Validate242
import NLM_PacketTypes
set_option autoImplicit false
noncomputable section
namespace NLM_RowSpec_242
open Aeneas Aeneas.Std Result AdapterRw NLM_Auth233 NLM_PacketTypes
abbrev Native (Ambient : Type) := Key → Slice Owned → Slice U8 → core.result.Result U64 PE →
 World Ambient → Observation Ambient NLM_Validate242.Event (core.result.Result r1_pool_adapter.ValidatedAsqa PE)
/-- Draft OPEN242 interface at the frozen signature. It retains the whole
nested source trace, complete Result and caller-frame at the SAME invocation.
Native internal-effect/allocator interpretation is still subject to review;
this is neither an admitted full child packet nor a positive row root. -/
def RowSpec_242 {Ambient : Type} (ops : Ops) (native : Native Ambient) : Prop :=
 ∀ program accounts bytes slot world,
 native program accounts bytes slot world = ⟨world,NLM_Validate242.G ops program accounts bytes slot⟩ ∧
 (native program accounts bytes slot world).run.result=
 r1_pool_adapter.owned.validate_asq8 ops program accounts bytes slot
#print RowSpec_242
end NLM_RowSpec_242
