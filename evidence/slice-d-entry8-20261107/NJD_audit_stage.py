from NJD_formal import *
for i,name in [(23,'NJD_ProofDriver'),(24,'NJD_ScanDriver')]:
 r=run('NJD_L%03d'%i,'lean',name);assert r['exit_status']==0
T='/home/dombarker/.elan/toolchains/leanprover--lean4---v4.32.0'
for i,name in [(25,'NJD_ProofDriver'),(26,'NJD_ScanDriver')]:
 r=ssh('cat '+B+'/NJD_native/'+name+'.c');assert r.returncode==0
 files={'NJD_native/'+name+'.c':r.stdout}
 for n in ['NFA_WALKER.c','NFA_MemoryLimit.c']:
  p='evidence/slice-d-entry6-20261107/NIS_'+n+'.xz'
  z=subprocess.check_output(['git','show','HEAD:'+p]);raw=lzma.decompress(z)
  files['NJD_native/'+n]=raw.decode()
  (E/('NJD_'+n+'.xz')).write_bytes(z);(E/('NJD_'+n+'.sha256')).write_text(sha(raw)+'\n')
 r=run('NJD_L%03d'%i,'link',name,[T+'/bin/lake','env','leanc','-O3','-rdynamic','-o','NJD_native/'+name,*files],files);assert r['exit_status']==0
files={n:(E/n).read_text() for n in ['NJD_AUDIT_ROOTS.json','NJD_EXPECTED_IMPORTS.jsonl','NJD_audit_one.py']};files['NJD_AUDIT_MODULES.json']=json.dumps([['NJD_COMBINED_IMPORT']])
for i,mode,name in [(27,'fixtures','NJD_ProofDriver'),(28,'proof0','NJD_ProofDriver'),(29,'scan','NJD_ScanDriver')]:
 r=run('NJD_L%03d'%i,'audit',mode,['python3','NJD_audit_one.py','NJD_native/'+name,mode],files)
 rr=ssh('python3',f'''from pathlib import Path
import json
b=Path({B!r});paths=list(b.glob('NEP_'+{mode!r}+'_*_REACHABLE.txt'))+[b/('NJD_binary_'+{mode!r}+'.json')]
if {mode!r}=='scan':paths+=[b/'NJD_LOADED_scan.jsonl']
print(json.dumps({{p.name:p.read_text() for p in paths if p.exists()}}))
''');assert rr.returncode==0,rr.stderr
 for n,t in json.loads(rr.stdout).items():
  p=E/('NJD_'+n)
  if n.endswith('.json'):p.write_text(t)
  else:p.with_name(p.name+'.xz').write_bytes(lzma.compress(t.encode()));p.with_name(p.name+'.sha256').write_text(sha(t.encode())+'\n')
 assert r['exit_status']==0
print('PASS_COMBINED_RAW32_FIXTURES8_SCAN',flush=True)
