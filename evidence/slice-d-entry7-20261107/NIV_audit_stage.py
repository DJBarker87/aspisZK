from NIV_formal import *
for i,name in [(27,'NIV_COMBINED_IMPORT'),(28,'NIV_ProofDriver'),(29,'NIV_ScanDriver')]:
 r=run('NIV_L%03d'%i,'lean',name);assert r['exit_status']==0
T='/home/dombarker/.elan/toolchains/leanprover--lean4---v4.32.0'
for i,name in [(30,'NIV_ProofDriver'),(31,'NIV_ScanDriver')]:
 r=ssh('cat '+B+'/NIV_native/'+name+'.c');assert r.returncode==0
 files={'NIV_native/'+name+'.c':r.stdout}
 for n in ['NFA_WALKER.c','NFA_MemoryLimit.c']:files['NIV_native/'+n]=lzma.decompress((E.parent/'slice-d-entry6-20261107'/('NIS_'+n+'.xz')).read_bytes()).decode()
 r=run('NIV_L%03d'%i,'link',name,[T+'/bin/lake','env','leanc','-O3','-rdynamic','-o','NIV_native/'+name,*files],files);assert r['exit_status']==0
files={n:(E/n).read_text() for n in ['NIV_AUDIT_ROOTS.json','NIV_EXPECTED_IMPORTS.jsonl','NIV_audit_one.py']};files['NIM_AUDIT_MODULES.json']=json.dumps([['NIV_COMBINED_IMPORT']])
for i,mode,name in [(32,'fixtures','NIV_ProofDriver'),(33,'proof0','NIV_ProofDriver'),(34,'scan','NIV_ScanDriver')]:
 r=run('NIV_L%03d'%i,'audit',mode,['python3','NIV_audit_one.py','NIV_native/'+name,mode],files)
 rr=ssh('python3',f'''from pathlib import Path
import json
b=Path({B!r});paths=list(b.glob('NEP_'+{mode!r}+'_*_REACHABLE.txt'))+[b/('NIV_binary_'+{mode!r}+'.json')]
if {mode!r}=='scan':paths+=[b/'NIV_LOADED_scan.jsonl']
print(json.dumps({{p.name:p.read_text() for p in paths if p.exists()}}))
''');assert rr.returncode==0,rr.stderr
 for n,t in json.loads(rr.stdout).items():
  p=E/('NIV_'+n)
  if n.endswith('.json'):p.write_text(t)
  else:p.with_name(p.name+'.xz').write_bytes(lzma.compress(t.encode()));p.with_name(p.name+'.sha256').write_text(sha(t.encode())+'\n')
 assert r['exit_status']==0
print('PASS_COMBINED_RAW36_FIXTURES8_SCAN',flush=True)
