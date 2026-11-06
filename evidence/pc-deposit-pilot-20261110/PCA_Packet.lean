import PCA_Event
set_option autoImplicit false
namespace PCA
/-- Typed OPEN interface schema only: native/ref binders must be instantiated
by the child's frozen-body certificate and reviewed exact reference. Equality
retains full Result, ordered effects, abort state and every account frame.
This definition is not itself a complete row packet or an E5 discharge. -/
def FullPacket {Args Reply : Type}
    (native reference : Args → PCA_State → Execution Reply) : Prop :=
  ∀ (args : Args) (before : PCA_State), native args before = reference args before
end PCA
