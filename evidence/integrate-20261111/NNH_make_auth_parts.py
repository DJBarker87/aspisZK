from pathlib import Path
import json,hashlib
base=Path('evidence/integrate-20261111');path=base/'NNH_AuthNativeFission.lean';s=path.read_text();start=s.index('def tail');stop=s.index('\ndef head',start);full=s[start:stop];lines=full.splitlines();body=next(i for i,l in enumerate(lines) if l.startswith('  let r6'));common='''(ops : Ops) (verifier_program : solana_pubkey.Pubkey)
 (master_account checkpoint_account lane_account registry_account entry_account : r1_pool_adapter.owned.OwnedAccount)
 (pool_program : solana_pubkey.Pubkey) (output_lane : U8) (current_slot : U64)''';arg='ops verifier_program master_account checkpoint_account lane_account registry_account entry_account pool_program output_lane current_slot';ret='Result (core.result.Result r1_pool_adapter.AuthenticatedAsq8Accounts solana_program_error.ProgramError)'
masterT='aspis_statement.pool_v1.pair_forest_accounts.PoolV1PairForestMasterV1';ckT='aspis_statement.pool_v1.pair_forest_accounts.PoolV1PairForestCheckpointV1'
def take(keyword):
 k=next(i for i,l in enumerate(lines) if l.strip()==keyword);depth=len(lines[k])-len(lines[k].lstrip());j=next(i for i in range(k+1,len(lines)) if lines[i].strip() and len(lines[i])-len(lines[i].lstrip())<depth);return k,j,depth
ckS,ckE,ckD=take('let r11 ←');laS,laE,laD=take('let r15 ←')
laneBody='\n'.join('  '+l[laD:] for l in lines[laS:laE])
ckBody='\n'.join('  '+l[ckD:] for l in lines[ckS:laS]+[' '*laD+'lane '+arg+' p val1 val4 p2']+lines[laE:ckE])
masterBody='\n'.join(lines[body:ckS]+[' '*ckD+'checkpoint '+arg+' p val1']+lines[ckE:])
header='''import NNH_AuthNativeFission
set_option autoImplicit false
noncomputable section
namespace NNH_AuthTailParts
open Aeneas Aeneas.Std Result ControlFlow Error AdapterRw
'''
lane='def lane '+common+' (p : solana_pubkey.Pubkey) (val1 : '+masterT+') (val4 : '+ckT+') (p2 : solana_pubkey.Pubkey) : '+ret+' := do\n'+laneBody+'\n'
ck='def checkpoint '+common+' (p : solana_pubkey.Pubkey) (val1 : '+masterT+') : '+ret+' := do\n'+ckBody+'\n'
master='def master '+common+' : '+ret+' := do\n'+masterBody+'\n'
th='\ntheorem source '+common+' : NNH_AuthNativeFission.tail '+arg+' = master '+arg+' := by rfl\n#print axioms source\nend NNH_AuthTailParts\n'
(base/'NNH_AuthTailParts.lean').write_text(header+lane+'\n'+ck+'\n'+master+th)
(base/'NNH_AUTH_PARTS.json').write_text(json.dumps(dict(source=str(path),sha256=hashlib.sha256(path.read_bytes()).hexdigest(),checkpoint=[ckS,ckE,ckD],lane=[laS,laE,laD],scope='Model equality only; no native row credit'),indent=2)+'\n')
