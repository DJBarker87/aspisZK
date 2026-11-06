from NJN_formal import *
for i,name in [(16,'NJN_ProofDriver'),(17,'NJN_ScanDriver')]:
 r=run('NJN_L%03d'%i,'lean',name);assert r['exit_status']==0
T='/home/dombarker/.elan/toolchains/leanprover--lean4---v4.32.0'
for i,name in [(18,'NJN_ProofDriver'),(19,'NJN_ScanDriver')]:
 r=ssh('cat '+B+'/NJN_native/'+name+'.c');assert r.returncode==0
 files={'NJN_native/'+name+'.c':r.stdout}
 for n in ['NFA_WALKER.c','NFA_MemoryLimit.c']:
  p='evidence/slice-d-entry6-20261107/NIS_'+n+'.xz'
  z=subprocess.check_output(['git','show','HEAD:'+p]);raw=lzma.decompress(z)
  files['NJN_native/'+n]=raw.decode()
  (E/('NJN_'+n+'.xz')).write_bytes(z);(E/('NJN_'+n+'.sha256')).write_text(sha(raw)+'\n')
 r=run('NJN_L%03d'%i,'link',name,[T+'/bin/lake','env','leanc','-O3','-rdynamic','-o','NJN_native/'+name,*files],files);assert r['exit_status']==0
files={n:(E/n).read_text() for n in ['NJN_AUDIT_ROOTS.json','NJN_EXPECTED_IMPORTS.jsonl','NJN_audit_one.py']};files['NJN_AUDIT_MODULES.json']=json.dumps([['NJN_COMBINED_IMPORT']])
for i,mode,name in [(20,'fixtures','NJN_ProofDriver'),(21,'proof0','NJN_ProofDriver'),(22,'scan','NJN_ScanDriver')]:
 r=run('NJN_L%03d'%i,'audit',mode,['python3','NJN_audit_one.py','NJN_native/'+name,mode],files)
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
print('PASS_COMBINED_RAW32_FIXTURES8_SCAN',flush=True)
