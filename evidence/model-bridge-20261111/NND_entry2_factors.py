from pathlib import Path
import re
E=Path(__file__).resolve().parent
src='NND_RegistryV2EntryFactor'
def cut(new,name,start,indent,stop,args,call):
 global src
 s=(E/(src+'.lean')).read_text();s=s[s.index('def run'):s.index('\ntheorem source')]
 a=s.index(' '*indent+start);b=a+re.search(stop,s[a:],re.M).start()
 leaf=s[a:b].rstrip();leaf='\n'.join('  '+x[indent:] if x.startswith(' '*indent) else x for x in leaf.splitlines())
 header=f'''import {src}
import NND_Entry2ValueRSL
set_option autoImplicit false
noncomputable section
namespace {name}
open Aeneas Aeneas.Std Result ControlFlow Error AdapterRw NND_Carrier NND_Returned
'''
 (E/(name+'.lean')).write_text(header+'def run '+args+' : Result (core.result.Result Unit solana_program_error.ProgramError) := do\n'+leaf+f'\n\nend {name}\nend\n')
 allargs=s[s.index('(ops :'):s.index(' : Result')]
 body=s[:a]+' '*indent+name+'.run '+call+'\n'+s[b:]
 params='ops verifier_program pool_program master_account master registry_account entry_account current_slot registry_program loader val1'
 (E/(new+'.lean')).write_text(header.replace('import '+src,'import '+name).replace('namespace '+name,'namespace '+new)+body+'\ntheorem source '+allargs+' :\n '+src+'.run '+params+' = run '+params+f' := rfl\n\n#print axioms source\nend {new}\nend\n')
 src=new
cut('NND_RegistryV2ProgramdataFactor','NND_Entry2Programdata','let s11 ←',34,r'^ {30}\|', '''(ops : Ops) (verifier_program p loader : solana_pubkey.Pubkey)
 (current_slot : U64) (a6 : Array U8 32#usize)
 (val5 : aspis_statement.pool_v1.verifier_registry.VerifierRegistryEntryV2)''','ops verifier_program p loader current_slot a6 val5')
cut('NND_RegistryV2ExpectedFactor','NND_Entry2Expected','let p2 ←',32,r'^ {30}\|', '''(ops : Ops) (verifier_program p loader : solana_pubkey.Pubkey)
 (entry_account : r1_pool_adapter.owned.OwnedAccount) (current_slot : U64) (a6 : Array U8 32#usize)
 (val5 : aspis_statement.pool_v1.verifier_registry.VerifierRegistryEntryV2) (val6 : solana_pubkey.Pubkey)''','ops verifier_program p loader entry_account current_slot a6 val5 val6')
cut('NND_RegistryV2PdaFactor','NND_Entry2Pda','let s6 ←',30,r'^ {28}\|', '''(ops : Ops) (verifier_program p registry_program loader : solana_pubkey.Pubkey)
 (entry_account : r1_pool_adapter.owned.OwnedAccount) (current_slot : U64) (a6 : Array U8 32#usize)
 (val5 : aspis_statement.pool_v1.verifier_registry.VerifierRegistryEntryV2)''','ops verifier_program p registry_program loader entry_account current_slot a6 val5')
cut('NND_RegistryV2DecodeFactor','NND_Entry2Decode','let r11 ←',26,r'^ {24}\|', '''(ops : Ops) (verifier_program p registry_program loader : solana_pubkey.Pubkey)
 (entry_account : r1_pool_adapter.owned.OwnedAccount) (current_slot : U64) (a6 : Array U8 32#usize)''','ops verifier_program p registry_program loader entry_account current_slot a6')
cut('NND_RegistryV2ReadonlyFactor','NND_Entry2Readonly','let r10 ←',24,r'^ {20}else$', '''(ops : Ops) (verifier_program p registry_program loader : solana_pubkey.Pubkey)
 (entry_account : r1_pool_adapter.owned.OwnedAccount) (current_slot : U64) (a6 : Array U8 32#usize)''','ops verifier_program p registry_program loader entry_account current_slot a6')
cut('NND_RegistryV2GuardFactor','NND_Registry2Guard','let a4 ← ops.op39 p',8,r'^ {6}\|', '''(ops : Ops) (verifier_program p registry_program loader : solana_pubkey.Pubkey)
 (master : aspis_statement.pool_v1.pair_forest_accounts.PoolV1PairForestMasterV1)
 (entry_account : r1_pool_adapter.owned.OwnedAccount) (current_slot : U64)
 (val1 : aspis_statement.pool_v1.verifier_registry.VerifierRegistryV2) (val3 : solana_pubkey.Pubkey)''','ops verifier_program p registry_program loader master entry_account current_slot val1 val3')
cut('NND_RegistryV2ProgramFactor','NND_Registry2Program','let s3 ←',6,r'^ {2}\|', '''(ops : Ops) (verifier_program p registry_program loader : solana_pubkey.Pubkey)
 (master : aspis_statement.pool_v1.pair_forest_accounts.PoolV1PairForestMasterV1)
 (entry_account : r1_pool_adapter.owned.OwnedAccount) (current_slot : U64)
 (val1 : aspis_statement.pool_v1.verifier_registry.VerifierRegistryV2)''','ops verifier_program p registry_program loader master entry_account current_slot val1')
cut('NND_RegistryV2ExpectedFactor2','NND_Registry2Expected','let p1 ←',4,r'^ {2}\|', '''(ops : Ops) (verifier_program p registry_program loader : solana_pubkey.Pubkey)
 (master : aspis_statement.pool_v1.pair_forest_accounts.PoolV1PairForestMasterV1)
 (registry_account entry_account : r1_pool_adapter.owned.OwnedAccount) (current_slot : U64)
 (val1 : aspis_statement.pool_v1.verifier_registry.VerifierRegistryV2) (val2 : solana_pubkey.Pubkey)''','ops verifier_program p registry_program loader master registry_account entry_account current_slot val1 val2')
