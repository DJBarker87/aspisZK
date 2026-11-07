import PCM_Witness
import PCM_StepLaws
import PCM_Vault
set_option autoImplicit false
namespace PCM_POOL_389
open RSL PCM PCM.Computation PCM.Vault
abbrev Args := B32 × B32 × PoolIdentity × List AccountInfo × B32 × UInt32 × Option (UInt8 × UInt8)
abbrev Children := PCM.Vault.Children

def Ref (C : Children) (a : Args) : Computation WithdrawalPlan := do
  let (program,pool,identity,accounts,destination,amount32,hints) := a
  let (ma,va,da,authority,tokenProgram) ← five accounts
  check (amount32 == 0) (.custom 0x41532030)
  check (tokenProgramBad identity tokenProgram) (.custom 0x41532013)
  let expectedMint := identity.asset_mint
  check (ma.key != expectedMint) (.custom 0x41532014)
  C.ownedAccount.call (ma,false)
  let mint ← readMint C ma
  C.ownedAccount.call (va,true)
  C.ownedAccount.call (da,true)
  let (expectedAuthority,bump) ← match hints with
    | none => C.authorityAddress.call (program,pool)
    | some h => do
      let matched ← C.storedBumpMatches.call (["aspis-pool-vault-authority-v1".toUTF8.toList,pool.bytes,[h.1]],program,authority.key)
      check (!matched) (.custom 0x41532016)
      Computation.pure (authority.key,h.1)
  let s ← get
  check (authority.key != expectedAuthority || s.owners authority.cell != SYSTEM_PROGRAM ||
    authority.executable || authority.is_signer || authority.is_writable) (.custom 0x41532016)
  let empty ← dataIsEmpty authority
  check (!empty) (.custom 0x41532016)
  check (da.key != destination) (.custom 0x41532032)
  let vault ← readToken C va
  let destinationState ← readToken C da
  let vaultOk ← match hints with
    | some h => C.storedBumpMatches.call (["aspis-pool-vault-token-v1".toUTF8.toList,pool.bytes,[h.2]],program,va.key)
    | none => do let (expected,_) ← C.vaultAddress.call (program,pool); Computation.pure (va.key == expected)
  check (!vaultOk) (.custom 0x41532017)
  check (vault.mint != expectedMint || destinationState.mint != expectedMint || vault.authority != expectedAuthority) (.custom 0x41532015)
  check (vault.has_delegate || vault.is_native || vault.delegated_amount != 0 || vault.has_close_authority || destinationState.is_native) (.custom 0x4153201a)
  let amount := amount32.toUInt64
  check (decide (vault.amount < amount)) (.custom 0x41532031)
  let vaultAfter := vault.amount - amount
  check (decide (0xffffffffffffffff - destinationState.amount < amount)) (.custom 0x41532008)
  let destinationAfter := destinationState.amount + amount
  let instruction ← newInstruction va.key ma.key da.key authority.key amount mint.decimals
  Computation.pure ⟨instruction,ma.key,va.key,da.key,authority.key,amount,vault.amount,vaultAfter,destinationState.amount,destinationAfter,mint.decimals,bump⟩

def RowSpec (C : Children) (impl : Args → State → Env → Observation WithdrawalPlan) : Prop :=
  PCM.RowSpec (fun _ => True) (Ref C) impl

theorem rejects_wrong_error (C : Children) :
    ¬ RowSpec C (fun _ s _ => ⟨.ret (.error .invalidArgument,s),[]⟩) := by
  let a : Args := ⟨zero32,zero32,PCM.identity0,[],zero32,0,none⟩
  apply PCM.rejects_error (fun _ : Args => True) (Ref C) a (.notEnoughAccountKeys) .invalidArgument trivial
  · unfold Ref
    exact PCM.Computation.bind_throw _ _
  · intro h; cases h
#print axioms rejects_wrong_error
end PCM_POOL_389
