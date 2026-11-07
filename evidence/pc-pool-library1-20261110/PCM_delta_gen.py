from pathlib import Path
E=Path(__file__).resolve().parent
for n,plan,bindings,keys,reads,condition in [
 (395,'TransferPlan','ma,sa,authority,va,token','ma.key != plan.mint || sa.key != plan.source || authority.key != plan.authority || va.key != plan.vault || token.key != TOKEN_ID','let source ← readToken C sa\n  let vault ← readToken C va','source.mint != plan.mint || vault.mint != plan.mint || source.authority != plan.authority || source.amount != plan.source_after || vault.amount != plan.vault_after'),
 (396,'WithdrawalPlan','ma,va,da,authority,token','ma.key != plan.mint || va.key != plan.vault || da.key != plan.destination || authority.key != plan.authority || token.key != TOKEN_ID','let vault ← readToken C va\n  let destination ← readToken C da','vault.mint != plan.mint || destination.mint != plan.mint || vault.authority != plan.authority || vault.amount != plan.vault_after || destination.amount != plan.destination_after')]:
 (E/f'PCM_Spec_POOL_{n}.lean').write_text(f'''import PCM_Vault
set_option autoImplicit false
namespace PCM_POOL_{n}
open RSL PCM PCM.Computation PCM.Vault
abbrev Args := List AccountInfo × {plan}
def Ref (C : PCM.Vault.Children) (a : Args) : Computation Unit := do
  let (accounts,plan) := a
  let ({bindings}) ← five accounts
  check ({keys}) (.custom 0x4153201c)
  {reads}
  check ({condition}) (.custom 0x4153201c)
def RowSpec (C : PCM.Vault.Children) (impl : Args → State → Env → Observation Unit) : Prop :=
  PCM.RowSpec (fun _ => True) (Ref C) impl
end PCM_POOL_{n}
''')
print('PCM post-CPI delta specifications emitted')
