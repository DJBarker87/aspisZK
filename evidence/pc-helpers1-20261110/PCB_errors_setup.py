"""Scratch-only actual-function contracts and references; every native arm retained."""
from pathlib import Path
import subprocess,json,difflib,re
E=Path(__file__).resolve().parent;REV='4bb3b3f51e16b4525f1d10336e2b0bcbbd775387'
entries=[('159','authorization_receipt','PoolV1VerifierDispatchFormatError','PoolV1AuthorizationReceiptError','Dispatch'),('160','authorization_receipt_account','PoolV1AuthorizationReceiptError','PoolV1AuthorizationReceiptAccountErrorV1','Receipt'),('189','pair_forest_accounts','PoolV1TreeError','PoolV1PairForestAccountErrorV1','Tree')]
files={};patch='';mapping=[]
for id,stem,inp,out,ctor in entries:
 path=f'crates/aspis-statement/src/pool_v1/{stem}.rs';orig=subprocess.check_output(['git','show',REV+':'+path],text=True)
 needle=f'impl From<{inp}> for {out} {{\n    fn from('
 attr=f'''impl From<{inp}> for {out} {{
    #[cfg_attr(all(kani,not(PCB_NEG_{id})), kani::ensures(|r| *r == PCB_{id}::reference(error)))]
    #[cfg_attr(all(kani,PCB_NEG_{id}), kani::ensures(|r| *r != PCB_{id}::reference(error)))]
    fn from('''
 assert needle in orig
 s=orig.replace(needle,attr)+f'\n#[cfg(any(kani,PCB_EXTRACT))]\n#[path="PCB_{id}.rs"]\nmod PCB_{id};\n'
 (E/f'PCB_{stem}.rs.txt').write_text(s);files['PCB_src/'+path]=f'PCB_{stem}.rs.txt'
 reference=f'''use super::*;
pub(super) fn reference(error:{inp})->{out} {{ {out}::{ctor}(error) }}
#[cfg(kani)]
#[kani::proof_for_contract(<{out} as From<{inp}>>::from)]
fn error_contract() {{let _=<{out} as From<{inp}>>::from(kani::any());}}
'''
 (E/f'PCB_{id}.rs').write_text(reference);files['PCB_src/'+str(Path(path).parent/f'PCB_{id}.rs')]=f'PCB_{id}.rs'
 patch+=''.join(difflib.unified_diff(orig.splitlines(True),s.splitlines(True),fromfile='a/'+path,tofile='b/'+path))
 mapping.append(dict(id='POOL:'+id,input=inp,output=out,constructor=ctor,domain='all valid input enum constructors including every payload constructor',modifies=[]))
# Derive arbitrary only in cfg(kani), all variants/payloads; no hand-picked enum tags.
for stem,enum in [('verifier_dispatch','PoolV1VerifierDispatchFormatError'),('authorization_receipt','PoolV1AuthorizationReceiptError'),('incremental_merkle','PoolV1TreeError')]:
 path=f'crates/aspis-statement/src/pool_v1/{stem}.rs';orig=subprocess.check_output(['git','show',REV+':'+path],text=True)
 p=E/f'PCB_{stem}.rs.txt';s=p.read_text() if p.exists() else orig
 assert 'pub enum '+enum in s;s=s.replace('pub enum '+enum,'#[cfg_attr(kani,derive(kani::Arbitrary))]\npub enum '+enum)
 p.write_text(s);files['PCB_src/'+path]=p.name
 # Rebuild full patch below using final sources.
patch=''
for n,p in files.items():
 if not p.endswith('.rs.txt'):continue
 path=n[len('PCB_src/'):];orig=subprocess.check_output(['git','show',REV+':'+path],text=True);s=(E/p).read_text()
 patch+=''.join(difflib.unified_diff(orig.splitlines(True),s.splitlines(True),fromfile='a/'+path,tofile='b/'+path))
(E/'PCB_ERRORS.patch').write_text(patch);(E/'PCB_ERROR_MAPPING.json').write_text(json.dumps(mapping,indent=1)+'\n')
t=json.loads((E/'PCB_TASKS.json').read_text());B='/home/dombarker/project-offloads/codex-pc-helpers1-20261110'
for i,id in enumerate(['159','160','189']):
 for negative in [False,True]:
  num=8+2*i+int(negative);a=f'PCB_K{num:03}';x=json.loads(json.dumps(t['PCB_K006']));x['files']={'PCB_gate.py':'PCB_gate.py',**files};x['target']=f'POOL:{id} '+('inverted control' if negative else 'actual From contract');x['command']=['python3','PCB_gate.py',a+'.json'];stem=entries[i][1];x['native_command'][x['native_command'].index('--harness')+1]=f'pool_v1::{stem}::PCB_{id}::error_contract';x['collect']=[n.replace('PCB_K006',a) for n in x['collect']]
  if negative:x['env']={'RUSTFLAGS':f'-C link-arg=-Wl,--threads=1 --cfg PCB_NEG_{id}'}
  t[a]=x
(E/'PCB_TASKS.json').write_text(json.dumps(t,indent=1)+'\n')
print('PCB error contracts prepared:159,160,189; full native enum domains')
