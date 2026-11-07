import PCM_Witness
import PCM_StepLaws
import PCM_Vault
set_option autoImplicit false
namespace PCM_POOL_388
open RSL PCM PCM.Computation PCM.Vault
abbrev Args := B32 × B32 × PoolIdentity × List AccountInfo × UInt32
abbrev Children := PCM.Vault.Children

def Ref (C : Children) (a : Args) : Computation TransferPlan := do
  let (program,pool,identity,accounts,amount32) := a
  let (ma,sa,authority,va,tokenProgram) ← five accounts
  check (tokenProgramBad identity tokenProgram) (.custom 0x41532013)
  let expectedMint := identity.asset_mint
  check (ma.key != expectedMint) (.custom 0x41532014)
  C.ownedAccount.call (ma,false)
  let mint ← readMint C ma
  C.ownedAccount.call (sa,true)
  C.ownedAccount.call (va,true)
  check (!authority.is_signer || authority.is_writable || authority.executable) (.custom 0x4153201d)
  let source ← readToken C sa
  let vault ← readToken C va
  check (source.mint != expectedMint || vault.mint != expectedMint || source.authority != authority.key) (.custom 0x41532015)
  let (expectedVault,_) ← C.vaultAddress.call (program,pool)
  check (va.key != expectedVault) (.custom 0x41532017)
  let (expectedAuthority,_) ← C.authorityAddress.call (program,pool)
  check (vault.authority != expectedAuthority) (.custom 0x41532016)
  check (vault.has_delegate || vault.is_native || vault.delegated_amount != 0 || vault.has_close_authority) (.custom 0x4153201a)
  let amount := amount32.toUInt64
  check (decide (source.amount < amount)) (.custom 0x41532019)
  let sourceAfter := source.amount - amount
  check (decide (0xffffffffffffffff - vault.amount < amount)) (.custom 0x41532008)
  let vaultAfter := vault.amount + amount
  let instruction ← newInstruction sa.key ma.key va.key authority.key amount mint.decimals
  Computation.pure ⟨instruction,sa.key,ma.key,va.key,authority.key,amount,source.amount,sourceAfter,vault.amount,vaultAfter,mint.decimals⟩

def RowSpec (C : Children) (impl : Args → State → Env → Observation TransferPlan) : Prop :=
  PCM.RowSpec (fun _ => True) (Ref C) impl

theorem rejects_wrong_error (C : Children) :
    ¬ RowSpec C (fun _ s _ => ⟨.ret (.error .invalidArgument,s),[]⟩) := by
  let a : Args := ⟨zero32,zero32,PCM.identity0,[],0⟩
  apply PCM.rejects_error (fun _ : Args => True) (Ref C) a (.notEnoughAccountKeys) .invalidArgument trivial
  · unfold Ref
    exact PCM.Computation.bind_throw _ _
  · intro h; cases h
#print axioms rejects_wrong_error
end PCM_POOL_388
