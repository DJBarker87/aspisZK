from NJI_formal import *
T='/home/dombarker/.elan/toolchains/leanprover--lean4---v4.32.0'
name='NJI_ScanDriver'
r=ssh('cat '+B+'/NJI_native/'+name+'.c');assert r.returncode==0
files={'NJI_native/'+name+'.c':r.stdout}
for n in ['NFA_WALKER.c','NFA_MemoryLimit.c']:
 p=Path('evidence/slice-d-entry6-20261107')/('NIS_'+n+'.xz')
 raw=lzma.decompress(p.read_bytes());assert sha(raw)==p.with_suffix('.sha256').read_text().strip()
 files['NJI_native/'+n]=raw.decode()
rc=run('NJI_L060','link',name,[T+'/bin/lake','env','leanc','-O3','-rdynamic','-o','NJI_native/'+name,*files],files)
assert rc['exit_status']==0
proofhash='82898d45b249439ff7c1c6ed03b4c5c49d72888643aadc82896987c668613c76'
r=ssh('python3',f'''from pathlib import Path
import shutil,hashlib,json
src=Path('/home/dombarker/project-offloads/codex-cx-slice-d-entry6-20261107/NIS_native/NIS_ProofDriver');dst=Path({B!r})/'NJI_native/NJI_RetainedProofDriver'
assert hashlib.sha256(src.read_bytes()).hexdigest()=={proofhash!r};shutil.copy2(src,dst)
p=Path({B!r})/'NJI_native/NJI_ScanDriver';print(json.dumps(dict(proof_sha256={proofhash!r},proof_bytes=dst.stat().st_size,scan_sha256=hashlib.sha256(p.read_bytes()).hexdigest(),scan_bytes=p.stat().st_size)))
''');assert r.returncode==0
pins=json.loads(r.stdout);(E/'NJI_AUDIT_BINARIES.json').write_text(json.dumps(pins,indent=1)+'\n')
for a,mode,name,h in [('NJI_L061','proof0','NJI_RetainedProofDriver',proofhash),('NJI_L062','scan','NJI_ScanDriver',pins['scan_sha256'])]:
 files={'NIS_AUDIT_ROOTS.json':(E/'NJI_AUDIT_ROOTS.json').read_text(),'NIM_AUDIT_MODULES.json':json.dumps([['NJI_COMBINED_IMPORT']]),'NJI_EXPECTED_IMPORTS.jsonl':(E/'NJI_EXPECTED_IMPORTS.jsonl').read_text(),'NJI_audit_one.py':(E/'NJI_audit_one.py').read_text()}
 rc=run(a,'audit',mode,['python3','NJI_audit_one.py','NJI_native/'+name,mode,h],files)
 # Recover raw artifacts even when the scan rejects an import edge.
 r=ssh('python3',f'''from pathlib import Path
import json
b=Path({B!r});paths=list(b.glob('NEP_'+{mode!r}+'_*_REACHABLE.txt'))+[b/('NJI_binary_'+{mode!r}+'.json')]
if {mode!r}=='scan':paths+=[b/'NJI_LOADED_scan.jsonl']
print(json.dumps({{p.name:p.read_text() for p in paths if p.is_file()}}))
''');assert r.returncode==0
 for n,t in json.loads(r.stdout).items():
  p=E/('NJI_'+n)
  if n.endswith('.json'):p.write_text(t)
  else:p.with_name(p.name+'.xz').write_bytes(lzma.compress(t.encode()));p.with_name(p.name+'.sha256').write_text(sha(t.encode())+'\n')
 assert rc['exit_status']==0,(a,rc['exit_status'])
print('Combined audit1 collected',flush=True)
