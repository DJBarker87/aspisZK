from pathlib import Path
import json,subprocess
E=Path(__file__).resolve().parent;B='/home/dombarker/project-offloads/codex-pc-helpers2-20261110'
files=json.loads((E/'PCG_FROM_FILES.json').read_text())
# Append cfg-only reference modules; extracted references use the actual carriers.
p='programs/aspis-pool/src/instruction.rs';s=subprocess.check_output(['git','show','b936275465:'+p],text=True)
for row,src,dst,want,arms in [(287,'DepositInstructionFormatErrorV1','PoolInstructionFormatErrorV1','PoolInstructionFormatErrorV1::InvalidDeposit',list(json.loads((E.parent/'pc-helpers1-20261110/PCB_ERROR_MAPPING_287_288.json').read_text())['POOL:287'])),(288,'PoolInstructionFormatErrorV1','ProgramError','ProgramError::InvalidInstructionData',list(json.loads((E.parent/'pc-helpers1-20261110/PCB_ERROR_MAPPING_287_288.json').read_text())['POOL:288']))]:
 n=f'PCG_{row}.rs';t=f'use super::*;\npub(super) fn reference(_e:{src})->{dst}{{{want}}}\n'
 t+=f'#[cfg(kani)] #[kani::proof]\nfn all_arms(){{let tag:u8=kani::any();kani::assume(tag<{len(arms)});let e=match tag{{'+','.join(f'{i}=>{src}::{v}' for i,v in enumerate(arms))+',_=>unreachable!()};'
 t+=f'let got=<{dst} as From<{src}>>::from(e);let mut expected=reference(e);'
 bad='PoolInstructionFormatErrorV1::WrongLength' if row==287 else 'ProgramError::InvalidArgument'
 t+=f'if cfg!(PCG_NEG_{row}) && tag==0{{expected={bad};}}assert_eq!(got,expected);}}\n';(E/n).write_text(t)
 files['PCG_src/programs/aspis-pool/src/'+n]=n;s+=f'\n#[cfg(any(kani,PCG_EXTRACT))]\n#[path="{n}"]\nmod PCG_{row};\n'
(E/'PCG_instruction.rs.txt').write_text(s);files['PCG_src/'+p]='PCG_instruction.rs.txt'
# 159/160/189 do not need an Arbitrary derive: every payload arm is explicit.
t=json.loads((E/'PCG_TASKS.json').read_text());template=t['PCG_K001']
for j,row in enumerate([159,160,189,287,288]):
 for neg in [False,True]:
  a=f'PCG_K{8+2*j+int(neg):03}';x=json.loads(json.dumps(template));x['target']=f'POOL:{row} whole-domain From'+(' corrupted reference arm' if neg else '')
  x['files']={'PCG_gate.py':'PCG_gate.py',**files};x['command']=['python3','PCG_gate.py',a+'.json'];cmd=x['native_command'];cmd[cmd.index('--manifest-path')+1]=B+'/PCG_src/'+('programs/aspis-pool' if row>=287 else 'crates/aspis-statement')+'/Cargo.toml'
  if row<287:cmd[cmd.index('--features')+1]=x['pool_features']
  stem={159:'pool_v1::authorization_receipt',160:'pool_v1::authorization_receipt_account',189:'pool_v1::pair_forest_accounts',287:'instruction',288:'instruction'}[row]
  cmd[cmd.index('--harness')+1]=stem+f'::PCG_{row}::all_arms';x['env']={'RUSTFLAGS':'-C link-arg=-Wl,--threads=1'+(f' --cfg PCG_NEG_{row}' if neg else '')}
  x['collect']=[a+s for s in ['-graph-check.json','-graph.stderr','-lock-check.json','-source-check.json','-selected-features.txt']];x['expected_time']='Frozen dependency compilation then finite enum mapping; no field multiplication, copying or loops';t[a]=x
(E/'PCG_TASKS.json').write_text(json.dumps(t,indent=1)+'\n')
