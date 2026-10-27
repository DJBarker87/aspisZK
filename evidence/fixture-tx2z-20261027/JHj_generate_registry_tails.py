from pathlib import Path
import textwrap,re
R=Path(__file__).resolve().parents[2]
s=(R/'docs/research/100bit-spend-path-20261013/lean/AdapterRwModel.lean').read_text()
s=s[s.index('def r1_pool_adapter.owned.authenticate_invariant_release_registry (ops : Ops)'):]
s=s[:s.index('/-- [aspis_r1_cost_probe_program::r1_pool_adapter::owned::authenticate_asq8_accounts')]
lines=s.splitlines()
args='''(ops : Ops)
    (verifier_program pool_program : solana_pubkey.Pubkey)
    (master_account : r1_pool_adapter.owned.OwnedAccount)
    (master : aspis_statement.pool_v1.pair_forest_accounts.PoolV1PairForestMasterV1)
    (registry_account entry_account : r1_pool_adapter.owned.OwnedAccount) (current_slot : U64)'''
key='solana_pubkey.Pubkey';keybytes='Array U8 32#usize';reg='aspis_statement.pool_v1.verifier_registry.VerifierRegistryV2';entry='aspis_statement.pool_v1.verifier_registry.VerifierRegistryEntryV2'
types={'a2':keybytes,'registry_program':key,'loader':key,'val1':reg,'p':key,'s2':'Slice (Slice U8)','s5':'Slice (Slice U8)','val3':key,'a6':keybytes,'val5':entry,'s10':'Slice (Slice U8)','s13':'Slice (Slice U8)','val7':key}
entries=[('RegistryPolicy','let r ←',['a2']),('RegistryRead','let r3 ←',['registry_program','loader']),('RegistryDecoded','let p ←',['registry_program','loader','val1']),('RegistryPda','let r6 ←',['registry_program','loader','val1','p','s2']),('RegistryProgramdata','let r8 ←',['registry_program','loader','val1','p','s5']),('RegistryChecks','let a4 ← ops.op39 p',['registry_program','loader','val1','p','val3']),('RegistryStatus','let b11 ←',['registry_program','loader','val1','p','a6']),('EntryRead','let r11 ←',['registry_program','loader','p','a6']),('EntryDecoded','let s6 ←',['registry_program','loader','p','a6','val5']),('EntryPda','let r14 ←',['registry_program','loader','p','a6','val5','s10']),('EntryProgramdata','let r16 ←',['registry_program','loader','p','a6','val5','s13']),('EntryChecks','let a8 ← ops.op39 p',['registry_program','loader','p','a6','val5','val7'])]
for name,needle,free in entries:
 matches=[i for i,l in enumerate(lines) if l.strip()==needle]
 if not matches:
  print('MISSING',name,needle);continue
 start=matches[0];indent=len(lines[start])-len(lines[start].lstrip());end=start+1
 while end<len(lines) and (not lines[end].strip() or len(lines[end])-len(lines[end].lstrip())>=indent):end+=1
 body=textwrap.dedent('\n'.join(lines[start:end])).rstrip()
 out='import JHi_Authentication\nset_option autoImplicit false\nnoncomputable section\nnamespace AspisR1.JHj_'+name+'\nopen Aeneas Aeneas.Std Result\nopen _root_.AdapterRw\n'
 out+='\n/-- Verbatim immutable-registry caller continuation. No leaf association is assumed by this definition. -/\ndef run '+args+''.join('\n    ('+f+' : '+types[f]+')' for f in free)+' :\n    Result (core.result.Result Unit solana_program_error.ProgramError) := do\n'+textwrap.indent(body,'  ')+'\n#print axioms run\nend AspisR1.JHj_'+name+'\nend\n'
 (R/'lean'/('JHj_'+name+'.lean')).write_text(out)
