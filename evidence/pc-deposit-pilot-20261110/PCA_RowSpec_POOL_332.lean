import PCA_Packet
set_option autoImplicit false
namespace PCA
abbrev Args_POOL_332 := Nat
abbrev Reply_POOL_332 := Unit
/-- Frozen require_exact_account_count: len<expected maps to
NotEnoughAccountKeys; len>expected maps to InvalidArgument; equality returns
Ok. There are no child calls, loans, syscalls or Pool writes in this body. -/
def countReference (expected : Nat) (s : PCA_State) : Execution Unit :=
  ⟨s,[], if s.accountCount = expected then .ok ()
    else .error (.program (if s.accountCount < expected then notEnoughKeys else 2 * 2^32))⟩
def RowSpec_POOL_332 (native : Nat → PCA_State → Execution Unit) : Prop :=
  ∀ expected s, native expected s = countReference expected s
end PCA
