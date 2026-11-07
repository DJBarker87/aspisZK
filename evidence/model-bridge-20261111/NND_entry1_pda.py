from pathlib import Path
import re
E=Path(__file__).resolve().parent
s=(E/'NND_RegistryV1EntryFactor.lean').read_text();s=s[s.index('def run'):s.index('\ntheorem source')]
a=s.index('                      let s3 ←');b=a+re.search(r'^ {20}\|$',s[a:],re.M).start()
leaf=s[a:b].rstrip();leaf='\n'.join('  '+x[22:] if x.startswith(' '*22) else x for x in leaf.splitlines())
args='''(ops : Ops) (verifier_program p registry_program : solana_pubkey.Pubkey)
 (entry_account : r1_pool_adapter.owned.OwnedAccount) (current_slot : U64)
 (val4 : aspis_statement.pool_v1.verifier_registry.VerifierRegistryEntryV1)'''
header='''import NND_RegistryEntry1Value
import NND_PdaTransport
set_option autoImplicit false
noncomputable section
namespace NND_Entry1Pda
open Aeneas Aeneas.Std Result ControlFlow Error AdapterRw NND_Carrier NND_Returned
'''
out=header+'def run '+args+' : Result (core.result.Result Unit solana_program_error.ProgramError) := do\n'+leaf+'''

theorem source (base : Ops) (D : RSL.DeployedIds) (env : RSL.Env)
 (v p rp : solana_pubkey.Pubkey) (e : r1_pool_adapter.owned.OwnedAccount) (t : U64)
 (entry : aspis_statement.pool_v1.verifier_registry.VerifierRegistryEntryV1) :
 run (NND_RegistryOps.install base D env) v p rp e t entry =
 NND_FormatControl.thenCall (NND_RegistryOps.pda env (NND_PdaSeeds.entry1 p entry.bump) rp)
  (NND_RegistryEntry1Check.check (NND_RegistryOps.install base D env) v p e t entry) := by
 unfold run
 simp only [NND_RegistryScalarOps.as_ref,bind_tc_ok,lift]
 change _ = NND_FormatControl.thenCall ((NND_RegistryOps.install base D env).op38 (NND_PdaSeeds.entry1 p entry.bump) rp) _
 change _ = NND_FormatControl.thenCall (NND_RegistryOps.pda env (NND_PdaSeeds.entry1 p entry.bump) rp) _
 unfold NND_FormatControl.thenCall
 unfold NND_PdaSeeds.entry1 NND_PdaSeeds.one
 cases h : env.pda ((NND_PdaSeeds.entry1 p entry.bump).val.map bytes) (key rp) <;>
  (simp only [NND_RegistryOps.install,NND_RegistryOps.pda,NND_PdaSeeds.entry1,NND_PdaSeeds.one] at h ⊢
   simp only [h,bind_tc_ok]
   rfl)


#print axioms source
end NND_Entry1Pda
end
'''
(E/'NND_Entry1Pda.lean').write_text(out)
args=s[s.index('(ops :'):s.index(' : Result')]
body=s[:a]+'                      NND_Entry1Pda.run ops verifier_program p registry_program entry_account current_slot val4\n'+s[b:]
params='ops verifier_program pool_program master_account master registry_account entry_account current_slot registry_program val1'
(E/'NND_RegistryV1PdaFactor.lean').write_text(header.replace('import NND_RegistryEntry1Value','import NND_RegistryV1EntryFactor\nimport NND_Entry1Pda').replace('namespace NND_Entry1Pda','namespace NND_RegistryV1PdaFactor')+body+'\ntheorem source '+args+' :\n NND_RegistryV1EntryFactor.run '+params+' = run '+params+' := rfl\n\n#print axioms source\nend NND_RegistryV1PdaFactor\nend\n')
