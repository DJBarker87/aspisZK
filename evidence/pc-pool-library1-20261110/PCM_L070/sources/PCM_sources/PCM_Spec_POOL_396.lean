import PCM_Vault
set_option autoImplicit false
namespace PCM_POOL_396
open RSL PCM PCM.Computation PCM.Vault
abbrev Args := List AccountInfo × WithdrawalPlan
def Ref (C : PCM.Vault.Children) (a : Args) : Computation Unit := do
  let (accounts,plan) := a
  let (ma,va,da,authority,token) ← five accounts
  check (ma.key != plan.mint || va.key != plan.vault || da.key != plan.destination || authority.key != plan.authority || token.key != TOKEN_ID) (.custom 0x4153201c)
  let vault ← readToken C va
  let destination ← readToken C da
  check (vault.mint != plan.mint || destination.mint != plan.mint || vault.authority != plan.authority || vault.amount != plan.vault_after || destination.amount != plan.destination_after) (.custom 0x4153201c)
def RowSpec (C : PCM.Vault.Children) (impl : Args → State → Env → Observation Unit) : Prop :=
  PCM.RowSpec (fun _ => True) (Ref C) impl
end PCM_POOL_396
