import PCA_ValidatorReferences
set_option autoImplicit false
namespace PCA
abbrev Args_POOL_364 := Nat × Nat
abbrev Reply_POOL_364 := Unit
/-- OPEN exact helper target: full Result, unchanged state, no oracle/CPI/loan effects.
Native identity, call-site argument association, and the source/key equality
certificate remain unproved. This is not a CLOSED row. -/
def RowSpec_POOL_364 (native : Args_POOL_364 → PCA_State → Execution Unit) : Prop :=
  ∀ args s, native args s = payerSystemReference args s
end PCA
