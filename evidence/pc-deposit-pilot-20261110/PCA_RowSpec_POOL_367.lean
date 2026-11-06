import PCA_ValidatorReferences
set_option autoImplicit false
namespace PCA
abbrev Args_POOL_367 := Unit
abbrev Reply_POOL_367 := Unit
/-- OPEN exact helper target: full Result, unchanged state, no oracle/CPI/loan effects.
Native identity, call-site argument association, and the source/key equality
certificate remain unproved. This is not a CLOSED row. -/
def RowSpec_POOL_367 (native : Args_POOL_367 → PCA_State → Execution Unit) : Prop :=
  ∀ args s, native args s = uniqueReference args s
end PCA
