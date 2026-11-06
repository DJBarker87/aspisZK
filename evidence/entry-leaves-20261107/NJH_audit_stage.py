from NJH_formal import *
for i,name in [(20,'NJH_ProofDriver'),(21,'NJH_ScanDriver')]:
 r=run('NJH_L%03d'%i,'lean',name);assert r['exit_status']==0
T='/home/dombarker/.elan/toolchains/leanprover--lean4---v4.32.0'
for i,name in [(22,'NJH_ProofDriver'),(23,'NJH_ScanDriver')]:
 r=ssh('cat '+B+'/NJH_native/'+name+'.c');assert r.returncode==0
 files={'NJH_native/'+name+'.c':r.stdout}
 for n in ['NFA_WALKER.c','NFA_MemoryLimit.c']:
  p='evidence/slice-d-entry6-20261107/NIS_'+n+'.xz'
  z=subprocess.check_output(['git','show','HEAD:'+p]);raw=lzma.decompress(z)
  files['NJH_native/'+n]=raw.decode()
  (E/('NJH_'+n+'.xz')).write_bytes(z);(E/('NJH_'+n+'.sha256')).write_text(sha(raw)+'\n')
 r=run('NJH_L%03d'%i,'link',name,[T+'/bin/lake','env','leanc','-O3','-rdynamic','-o','NJH_native/'+name,*files],files);assert r['exit_status']==0
files={n:(E/n).read_text() for n in ['NJH_AUDIT_ROOTS.json','NJH_EXPECTED_IMPORTS.jsonl','NJH_audit_one.py']};files['NJH_AUDIT_MODULES.json']=json.dumps([['NJH_COMBINED_IMPORT']])
for i,mode,name in [(24,'fixtures','NJH_ProofDriver'),(25,'proof0','NJH_ProofDriver'),(26,'scan','NJH_ScanDriver')]:
 r=run('NJH_L%03d'%i,'audit',mode,['python3','NJH_audit_one.py','NJH_native/'+name,mode],files)
 rr=ssh('python3',f'''from pathlib import Path
import json
b=Path({B!r});paths=list(b.glob('NEP_'+{mode!r}+'_*_REACHABLE.txt'))+[b/('NJH_binary_'+{mode!r}+'.json')]
if {mode!r}=='scan':paths+=[b/'NJH_LOADED_scan.jsonl']
print(json.dumps({{p.name:p.read_text() for p in paths if p.exists()}}))
''');assert rr.returncode==0,rr.stderr
 for n,t in json.loads(rr.stdout).items():
  p=E/('NJH_'+n)
  if n.endswith('.json'):p.write_text(t)
  else:p.with_name(p.name+'.xz').write_bytes(lzma.compress(t.encode()));p.with_name(p.name+'.sha256').write_text(sha(t.encode())+'\n')
 assert r['exit_status']==0
print('PASS_COMBINED_RAW32_FIXTURES8_SCAN',flush=True)
