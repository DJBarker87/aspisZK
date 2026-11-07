from pathlib import Path
import hashlib,json
p=Path('evidence/integrate-20261111'); src=Path('evidence/tx2-auth-20261111/NMX_AdapterRwModel_source.txt');s=src.read_text();start=s.index('def r1_pool_adapter.owned.authenticate_asq8_accounts (ops : Ops)');end=s.index('\n/--',start);f=s[start:end]
lines=f.splitlines();k=next(i for i,l in enumerate(lines) if l.strip()=='let r6 ←');j=next(i for i in range(k+1,len(lines)) if lines[i].strip() and len(lines[i])-len(lines[i].lstrip())<16)
body='\n'.join('  '+l[16:] for l in lines[k:j])
params='ops verifier_program master_account checkpoint_account lane_account registry_account entry_account pool_program output_lane current_slot'
head='\n'.join(lines[:k]+['                tail '+params]+lines[j:]).replace('def r1_pool_adapter.owned.authenticate_asq8_accounts','def head')
header='''import NNH_AuthNativeGuards
set_option autoImplicit false
noncomputable section
namespace NNH_AuthNativeFission
open Aeneas Aeneas.Std Result ControlFlow Error AdapterRw

def tail (ops : Ops) (verifier_program : solana_pubkey.Pubkey)
 (master_account checkpoint_account lane_account registry_account entry_account : r1_pool_adapter.owned.OwnedAccount)
 (pool_program : solana_pubkey.Pubkey) (output_lane : U8) (current_slot : U64) :
 Result (core.result.Result r1_pool_adapter.AuthenticatedAsq8Accounts solana_program_error.ProgramError) := do
'''
theorem='''
theorem source (ops : Ops) (program : solana_pubkey.Pubkey)
 (accounts : Slice r1_pool_adapter.owned.OwnedAccount) (pool : solana_pubkey.Pubkey)
 (lane : U8) (slot : U64) :
 r1_pool_adapter.owned.authenticate_asq8_accounts ops program accounts pool lane slot =
 head ops program accounts pool lane slot := by rfl
#print axioms source
end NNH_AuthNativeFission
'''
(p/'NNH_AuthNativeFission.lean').write_text(header+body+'\n\n'+head+'\n'+theorem)
(p/'NNH_AUTH_NATIVE_FISSION.json').write_text(json.dumps(dict(source=str(src),sha256=hashlib.sha256(src.read_bytes()).hexdigest(),start_line=s[:start].count('\n')+1,first=k,last=j,method='Exact source fission, source theorem by definitional equality; no extraction or native row credit.'),indent=2)+'\n')
