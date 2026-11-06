import PCA_ValidatorReferences
set_option autoImplicit false
namespace PCA
abbrev Args_POOL_365 := Nat
abbrev Reply_POOL_365 := Unit
/-- OPEN exact helper target: full Result, unchanged state, no oracle/CPI/loan effects.
Native identity, call-site argument association, and the source/key equality
certificate remain unproved. This is not a CLOSED row. -/
def RowSpec_POOL_365 (native : Args_POOL_365 → PCA_State → Execution Unit) : Prop :=
  ∀ args s, native args s = tokenProgramReference args s
end PCA
