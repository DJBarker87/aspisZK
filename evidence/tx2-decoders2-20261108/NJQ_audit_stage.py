"""One optimized raw ax2/NFX audit of the checked support closure."""
from NJQ_formal import *
T='/home/dombarker/.elan/toolchains/leanprover--lean4---v4.32.0'
# Compile the only adapted driver; its full diff changes module/output lists only.
rc=run('NJQ_L069','lean','NJQ_ScanDriver',extra={'NJQ_native/.keep':'NJQ owned optimized audit outputs\n'});assert rc['exit_status']==0
r=ssh('cat '+B+'/NJQ_native/NJQ_ScanDriver.c');assert r.returncode==0
files={'NJQ_native/NJQ_ScanDriver.c':r.stdout}
for n in ['NFA_WALKER.c','NFA_MemoryLimit.c']:
 p=E.parent/'slice-d-entry6-20261107'/('NIS_'+n+'.xz');raw=lzma.decompress(p.read_bytes());assert sha(raw)==p.with_suffix('.sha256').read_text().strip();files['NJQ_native/'+n]=raw.decode()
rc=run('NJQ_L070','link','NJQ_ScanDriver',[T+'/bin/lake','env','leanc','-O3','-rdynamic','-o','NJQ_native/NJQ_ScanDriver',*files],files);assert rc['exit_status']==0
proofhash='82898d45b249439ff7c1c6ed03b4c5c49d72888643aadc82896987c668613c76'
r=ssh('python3',f'''from pathlib import Path
import shutil,hashlib,json
src=Path('/home/dombarker/project-offloads/codex-cx-tx2-decoders-20261107/NJI_native/NJI_RetainedProofDriver');dst=Path({B!r})/'NJQ_native/NJQ_RetainedProofDriver'
assert hashlib.sha256(src.read_bytes()).hexdigest()=={proofhash!r};shutil.copy2(src,dst)
p=Path({B!r})/'NJQ_native/NJQ_ScanDriver';print(json.dumps(dict(proof_sha256={proofhash!r},proof_bytes=dst.stat().st_size,scan_sha256=hashlib.sha256(p.read_bytes()).hexdigest(),scan_bytes=p.stat().st_size)))
''');assert r.returncode==0
pins=json.loads(r.stdout);(E/'NJQ_AUDIT_BINARIES.json').write_text(json.dumps(pins,indent=1)+'\n');(E/'NJQ_ProofDriver.diff').write_text('')
for a,mode,name,h in [('NJQ_L071','fixtures','NJQ_RetainedProofDriver',proofhash),('NJQ_L072','proof0','NJQ_RetainedProofDriver',proofhash),('NJQ_L073','scan','NJQ_ScanDriver',pins['scan_sha256'])]:
 files={'NIS_AUDIT_ROOTS.json':(E/'NJQ_AUDIT_ROOTS.json').read_text(),'NIM_AUDIT_MODULES.json':json.dumps([['NJQ_COMBINED_IMPORT']]),'NJQ_EXPECTED_IMPORTS.jsonl':(E/'NJQ_EXPECTED_IMPORTS.jsonl').read_text(),'NJQ_audit_one.py':(E/'NJQ_audit_one.py').read_text()}
 rc=run(a,'audit',mode,['python3','NJQ_audit_one.py','NJQ_native/'+name,mode,h],files)
 r=ssh('python3',f'''from pathlib import Path
import json
b=Path({B!r});paths=list(b.glob('NEP_'+{mode!r}+'_*_REACHABLE.txt'))+[b/('NJQ_binary_'+{mode!r}+'.json')]
if {mode!r}=='scan':paths+=[b/'NJQ_LOADED_scan.jsonl']
print(json.dumps({{p.name:p.read_text()for p in paths if p.is_file()}}))
''');assert r.returncode==0
 for n,t in json.loads(r.stdout).items():
  p=E/('NJQ_'+n)
  if n.endswith('.json'):p.write_text(t)
  else:p.with_name(p.name+'.xz').write_bytes(lzma.compress(t.encode()));p.with_name(p.name+'.sha256').write_text(sha(t.encode())+'\n')
 assert rc['exit_status']==0,(a,rc['exit_status'])
 print('NJQ audit mode '+mode+' collected',flush=True)
