"""Owned joint audit orchestration; unchanged hardened walker binary."""
from NKF_formal import *
import base64
T='/home/dombarker/.elan/toolchains/leanprover--lean4---v4.32.0'
# Existing binary is reused exactly, with the same eight fixture calibration.
proof='/home/dombarker/project-offloads/codex-cx-tx2-decoders2-20261107/NJQ_native/NJQ_RetainedProofDriver'
proofhash='82898d45b249439ff7c1c6ed03b4c5c49d72888643aadc82896987c668613c76'
result={}
def completed(a,target):
 rc=json.loads((E/a/'receipt.json').read_text())
 assert rc['exit_status']==0 and sha((E/(target+'.lean')).read_bytes()) in rc['source_hashes'].values()
 return rc['exit_status']
result['combined']=completed('NKF_L024','NKF_COMBINED_IMPORT')
result['scan_compile']=completed('NKF_L025','NKF_ScanDriver')
if result['scan_compile']==0:
 r=ssh('cat '+B+'/NKF_native/NKF_ScanDriver.c');assert r.returncode==0
 files={'NKF_native/NKF_ScanDriver.c':r.stdout}
 # Retrieve immutable predecessor C inputs from the committed SHA corpus.
 q='evidence/tx2-decoders2-20261108';get=lambda n:subprocess.check_output(['git','show','HEAD:'+q+'/'+n]);idx=json.loads(get('NJQ_INPUTS.json'))
 for n in ['NFA_WALKER.c','NFA_MemoryLimit.c']:
  h=idx['attempts']['NJQ_L070']['NJQ_native/'+n]
  raw=lzma.decompress(get(idx['objects'][h]['path']));assert sha(raw)==h
  files['NKF_native/'+n]=raw.decode()
 result['scan_link']=run('NKF_L026','link','NKF_ScanDriver',[T+'/bin/lake','env','leanc','-O3','-rdynamic','-o','NKF_native/NKF_ScanDriver',*files],files)['exit_status']
else:result['scan_link']='BLOCKED_COMPILE'
r=ssh('python3',f'''from pathlib import Path
import hashlib,json
p=Path({proof!r});assert hashlib.sha256(p.read_bytes()).hexdigest()=={proofhash!r};q=Path({B!r})/'NKF_native/NKF_ScanDriver';print(json.dumps(dict(proof_path=str(p),proof_sha256={proofhash!r},proof_bytes=p.stat().st_size,scan_sha256=hashlib.sha256(q.read_bytes()).hexdigest() if q.exists() else None,scan_bytes=q.stat().st_size if q.exists() else None)))
''');assert r.returncode==0
pins=json.loads(r.stdout);(E/'NKF_AUDIT_BINARIES.json').write_text(json.dumps(pins,indent=1)+'\n')
for a,mode,binary,h in [('NKF_L027','fixtures',proof,proofhash),('NKF_L028','proof0',proof,proofhash),('NKF_L029','scan','NKF_native/NKF_ScanDriver',pins['scan_sha256'])]:
 if mode=='scan' and result['scan_link']!=0:
  result[mode]='BLOCKED_LINK';continue
 if mode!='fixtures' and result['combined']!=0:
  result[mode]='BLOCKED_COMBINED';continue
 files={'NIS_AUDIT_ROOTS.json':(E/'NKF_AUDIT_ROOTS.json').read_text(),'NIM_AUDIT_MODULES.json':json.dumps([['NKF_COMBINED_IMPORT']]),'NKF_EXPECTED_IMPORTS.jsonl':(E/'NKF_EXPECTED_IMPORTS.jsonl').read_text(),'NKF_audit_one.py':(E/'NKF_audit_one.py').read_text()}
 rc=run(a,'audit',mode,['python3','NKF_audit_one.py',binary,mode,h],files);result[mode]=rc['exit_status']
 r=ssh('python3',f'''from pathlib import Path
import json
b=Path({B!r});paths=list(b.glob('NEP_'+{mode!r}+'_*_REACHABLE.txt'))+[b/('NKF_binary_'+{mode!r}+'.json')]
if {mode!r}=='scan':paths+=[b/'NKF_LOADED_scan.jsonl']
print(json.dumps({{p.name:p.read_text()for p in paths if p.is_file()}}))
''');assert r.returncode==0
 for n,t in json.loads(r.stdout).items():
  p=E/('NKF_'+n)
  if n.endswith('.json'):p.write_text(t)
  else:p.with_name(p.name+'.xz').write_bytes(lzma.compress(t.encode()));p.with_name(p.name+'.sha256').write_text(sha(t.encode())+'\n')
 (E/'NKF_JOINT_STATUS.json').write_text(json.dumps(result,indent=1)+'\n')
print(json.dumps(result))
