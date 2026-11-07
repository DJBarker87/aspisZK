import PCM_Vault
set_option autoImplicit false
namespace PCM_POOL_395
open RSL PCM PCM.Computation PCM.Vault
abbrev Args := List AccountInfo × TransferPlan
def Ref (C : PCM.Vault.Children) (a : Args) : Computation Unit := do
  let (accounts,plan) := a
  let (ma,sa,authority,va,token) ← five accounts
  check (ma.key != plan.mint || sa.key != plan.source || authority.key != plan.authority || va.key != plan.vault || token.key != TOKEN_ID) (.custom 0x4153201c)
  let source ← readToken C sa
  let vault ← readToken C va
  check (source.mint != plan.mint || vault.mint != plan.mint || source.authority != plan.authority || source.amount != plan.source_after || vault.amount != plan.vault_after) (.custom 0x4153201c)
def RowSpec (C : PCM.Vault.Children) (impl : Args → State → Env → Observation Unit) : Prop :=
  PCM.RowSpec (fun _ => True) (Ref C) impl
end PCM_POOL_395
