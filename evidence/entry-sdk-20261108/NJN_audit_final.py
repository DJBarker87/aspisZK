from NJN_formal import *
r=run('NJN_L026','lean','NJN_COMBINED_IMPORT');assert r['exit_status']==0
files={n:(E/n).read_text() for n in ['NJN_AUDIT_ROOTS.json','NJN_EXPECTED_IMPORTS.jsonl','NJN_audit_one.py']};files['NJN_AUDIT_MODULES.json']=json.dumps([['NJN_COMBINED_IMPORT']])
for i,mode,name in [(27,'proof0','NJN_ProofDriver'),(28,'scan','NJN_ScanDriver')]:
 r=run(f'NJN_L{i:03d}','audit',mode,['python3','NJN_audit_one.py','NJN_native/'+name,mode],files)
 rr=ssh('python3',f'''from pathlib import Path
import json
b=Path({B!r});paths=list(b.glob('NEP_'+{mode!r}+'_*_REACHABLE.txt'))+[b/('NJN_binary_'+{mode!r}+'.json')]
if {mode!r}=='scan':paths+=[b/'NJN_LOADED_scan.jsonl']
print(json.dumps({{p.name:p.read_text() for p in paths if p.exists()}}))
''');assert rr.returncode==0,rr.stderr
 for n,t in json.loads(rr.stdout).items():
  p=E/('NJN_'+n)
  if n.endswith('.json'):p.write_text(t)
  else:p.with_name(p.name+'.xz').write_bytes(lzma.compress(t.encode()));p.with_name(p.name+'.sha256').write_text(sha(t.encode())+'\n')
 assert r['exit_status']==0
print('NJN second/final combined raw/scan complete; fixture binary unchanged')
