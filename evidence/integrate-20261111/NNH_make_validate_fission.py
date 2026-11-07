from pathlib import Path
import hashlib,json
base=Path('evidence/integrate-20261111');src=Path('evidence/tx2-auth-20261111/NMX_AdapterRwModel_source.txt');s=src.read_text();start=s.index('def r1_pool_adapter.owned.validate_asq8 (ops : Ops)');end=s.index('\n/--',start);f=s[start:end];lines=f.splitlines()
def take(word):
 k=next(i for i,l in enumerate(lines) if l.strip()==word);d=len(lines[k])-len(lines[k].lstrip());j=next(i for i in range(k+1,len(lines)) if lines[i].strip() and len(lines[i])-len(lines[i].lstrip())<d);return k,j,d
scanS,scanE,scanD=take('let o ← ops.op9 accounts');authS,authE,authD=take('let r4 ←')
scan='\n'.join('  '+l[scanD:] for l in lines[scanS:scanE])
auth='\n'.join('  '+l[authD:] for l in lines[authS:scanS]+[' '*scanD+'scan ops accounts val val3']+lines[scanE:authE])
head='\n'.join(lines[:authS]+[' '*authD+'authenticate ops verifier_program accounts val pool_program val1 val2']+lines[authE:]).replace('def r1_pool_adapter.owned.validate_asq8','def head')
header='''import NNH_AuthPort
import NNH_ReconstructValuePort
set_option autoImplicit false
noncomputable section
namespace NNH_ValidateFission
open Aeneas Aeneas.Std Result ControlFlow Error AdapterRw
'''
ret='Result (core.result.Result r1_pool_adapter.ValidatedAsqa solana_program_error.ProgramError)'
scanDef='def scan (ops : Ops) (accounts : Slice r1_pool_adapter.owned.OwnedAccount) (val : LIBB_PoolCarriers.Request) (val3 : r1_pool_adapter.AuthenticatedAsq8Accounts) : '+ret+' := do\n'+scan+'\n'
authDef='''def authenticate (ops : Ops) (verifier_program : solana_pubkey.Pubkey)
 (accounts : Slice r1_pool_adapter.owned.OwnedAccount) (val : LIBB_PoolCarriers.Request)
 (pool_program : solana_pubkey.Pubkey) (val1 : U8) (val2 : U64) : '''+ret+' := do\n'+auth+'\n'
th='''
theorem source (ops : Ops) (program : solana_pubkey.Pubkey)
 (accounts : Slice r1_pool_adapter.owned.OwnedAccount) (data : Slice U8)
 (clock : core.result.Result U64 solana_program_error.ProgramError) :
 r1_pool_adapter.owned.validate_asq8 ops program accounts data clock=head ops program accounts data clock := by rfl
#print axioms source
end NNH_ValidateFission
'''
(base/'NNH_ValidateFission.lean').write_text(header+scanDef+'\n'+authDef+'\n'+head+th)
(base/'NNH_VALIDATE_FISSION.json').write_text(json.dumps(dict(source=str(src),sha256=hashlib.sha256(src.read_bytes()).hexdigest(),line=s[:start].count('\n')+1,scan=[scanS,scanE,scanD],auth=[authS,authE,authD],scope='Exact model source fission, no native row credit'),indent=2)+'\n')
