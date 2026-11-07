import PV_FN_THREAD_f124
set_option autoImplicit false
noncomputable section
namespace PV_FN_THREAD_f361Provider124
open PV_EVHB_OwnerMachine PV_EVHB_OwnerHeap
/-- thread20: use the exact stated provider types, including its operational
all-branch Post and explicit full stores. This replaces the old consumer
interface for NEW f361 assembly; old proved consumer results are retained. -/
abbrev Input := PV_FN_THREAD_f124_BoxContract.Input PV_RJ4IDB.NativeEvent
abbrev Backend := PV_FN_THREAD_f124_BoxContract.Backend PV_RJ4IDB.NativeEvent
abbrev Pre := PV_FN_THREAD_f124.Pre
abbrev Post := PV_FN_THREAD_f124.Post
/-- Literally the provider's stated contract type. Its count-value
strengthening under thread19 remains separate, so no numeric count is inferred
from this dependency. This is not the f361 contract or a new f124 closure. -/
def Dependency : Prop :=
  ∀ (x : Input) (H : Backend) (resources : Resources) (encode : Encode)
    (shape : PV_THR2_TypedRepresentation_ArcInner.Shape), Pre x → Post x H resources encode shape
/-- Compiled statement compatibility, by direct use of the provider theorem.
No source Arc representation is repeated or inferred from a consumer shape. -/
theorem provider_statement : Dependency := PV_FN_THREAD_f124.contract
#print axioms provider_statement
end PV_FN_THREAD_f361Provider124
