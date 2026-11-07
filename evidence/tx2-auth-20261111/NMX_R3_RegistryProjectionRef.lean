import NMX_R3_RegistryProjection
set_option autoImplicit false
noncomputable section
namespace NMX_R3_RegistryProjectionRef
open RSL RSL.TX2_234 NMX_R3_RegistryProjection

theorem master_key (a : Args) : (args a).master_account.key = a.master_account.key := rfl
theorem registry_account (a : Args) : (args a).registry_account = account a.registry_account := rfl
theorem entry_account (a : Args) : (args a).entry_account = account a.entry_account := rfl
theorem account_key (a : OwnedAccount) : (account a).key = a.key := rfl
theorem verifier (a : Args) : (args a).verifier_program = a.verifier_program := rfl
theorem current_slot (a : Args) : (args a).current_slot = a.current_slot := rfl
theorem policy (a : Args) : (args a).master.verifier_policy = a.master.verifier_policy := master_policy _

theorem policy_bad (D : DeployedIds) (a : Args) : policyBad D (args a) = policyBad D a := by
 unfold policyBad
 rw [policy]
 rfl

theorem registry1_bad (a : Args) (r : RegistryV1) : registryV1Bad (args a) r = registryV1Bad a r := by
 unfold registryV1Bad
 rw [policy,master_key]

theorem registry2_bad (D : DeployedIds) (a : Args) (r : RegistryV2) (p : B32) :
 registryV2Bad D (args a) r p = registryV2Bad D a r p := by
 unfold registryV2Bad
 rw [policy,master_key]

theorem entry1_bad (a : Args) (e : EntryV1) : entryV1Bad (args a) e = entryV1Bad a e := rfl
theorem entry2_bad (a : Args) (e : EntryV2) (p : B32) : entryV2Bad (args a) e p = entryV2Bad a e p := rfl

theorem v1 (D : DeployedIds) (a : Args) :
 v1Branch LIBB_PoolLib.library D (args a) = v1Branch LIBB_PoolLib.library D a := by
 unfold v1Branch
 simp only [master_key,registry1_bad,entry1_bad,registry_account,entry_account,account_key,readonly]
 simp only [read_decode LIBB_PoolLib.library.decodeRegistryV1 NMX_R3_RegistryByteCut.registry1,
  read_decode LIBB_PoolLib.library.decodeEntryV1 NMX_R3_RegistryByteCut.entry1] <;> rfl

theorem v2 (D : DeployedIds) (a : Args) :
 immutableBranch LIBB_PoolLib.library D (args a) = immutableBranch LIBB_PoolLib.library D a := by
 unfold immutableBranch
 simp only [master_key,registry2_bad,entry2_bad,registry_account,entry_account,account_key,verifier,readonly]
 simp only [read_decode LIBB_PoolLib.library.decodeRegistryV2 NMX_R3_RegistryByteCut.registry2,
  read_decode LIBB_PoolLib.library.decodeEntryV2 NMX_R3_RegistryByteCut.entry2] <;> rfl

/-- Equality of the COMPLETE reference relations, including both clone aborts
and every ordered PDA prefix. No representation bounds enter Domain. -/
theorem reference (D : DeployedIds) (a : Args) :
 Ref LIBB_PoolLib.library D (args a) = Ref LIBB_PoolLib.library D a := by
 unfold Ref
 simp only [policy_bad,policy,registry_account,readonly,v1,v2]

#print axioms master_key
#print axioms registry_account
#print axioms entry_account
#print axioms account_key
#print axioms verifier
#print axioms current_slot
#print axioms policy
#print axioms policy_bad
#print axioms registry1_bad
#print axioms registry2_bad
#print axioms entry1_bad
#print axioms entry2_bad
#print axioms v1
#print axioms v2
#print axioms reference
end NMX_R3_RegistryProjectionRef
end
