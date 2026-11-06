from PCA_formal import *
import lzma,base64
r=run('PCA_L055','lean','PCA_COMBINED_IMPORT');assert r['exit_status']==0,'Combined import failed; no unchanged rerun'
r=run('PCA_L056','lean','PCA_ProofDriver');assert r['exit_status']==0
r=ssh('cat '+B+'/PCA_native/PCA_ProofDriver.c');assert r.returncode==0
files={'PCA_native/PCA_ProofDriver.c':r.stdout}
for n in ['NFA_WALKER.c','NFA_MemoryLimit.c']:
 files['PCA_native/'+n]=lzma.decompress((E/('PCA_'+n+'.xz')).read_bytes()).decode()
T=json.loads((E/'PCA_ENV_BASE.json').read_text())['env']['LEAN_SYSROOT']
r=run('PCA_L057','link','PCA_ProofDriver',[T+'/bin/lake','env','leanc','-O3','-rdynamic','-o','PCA_native/PCA_ProofDriver',*files],files);assert r['exit_status']==0
runner='''from pathlib import Path
import sys,subprocess,hashlib,json
b=Path.cwd();binary=b/'PCA_native/PCA_ProofDriver';mode=sys.argv[1]
before=hashlib.sha256(binary.read_bytes()).hexdigest()
r=subprocess.run([str(binary),mode])
after=hashlib.sha256(binary.read_bytes()).hexdigest();assert before==after
(b/('PCA_binary_'+mode+'.json')).write_text(json.dumps(dict(binary=str(binary),before=before,after=after,unchanged=True,exit=r.returncode)))
sys.exit(r.returncode)
'''
(E/'PCA_audit_one.py').write_text(runner)
files={n:(E/n).read_text() for n in ['PCA_AUDIT_ROOTS.json','PCA_AUDIT_MODULES.json','PCA_EXPECTED_IMPORTS.jsonl']};files['PCA_audit_one.py']=runner
for a,mode in [(58,'fixtures'),(59,'proof0'),(60,'scan')]:
 r=run(f'PCA_L{a:03d}','audit',mode,['python3','PCA_audit_one.py',mode],files)
 rr=ssh('python3',f'''from pathlib import Path
import json,lzma,base64,hashlib
b=Path({B!r});names=list(b.glob('NEP_'+{mode!r}+'_*_REACHABLE.txt'))+[b/('PCA_binary_'+{mode!r}+'.json')]
if {mode!r}=='scan':names += [b/'PCA_LOADED_scan.jsonl']
out=[]
for p in names:
 if p.is_file():
  raw=p.read_bytes();out.append(dict(name=p.name,sha256=hashlib.sha256(raw).hexdigest(),bytes=len(raw),data=base64.b64encode(lzma.compress(raw)).decode()))
print(json.dumps(out))
''');assert rr.returncode==0,rr.stderr
 for x in json.loads(rr.stdout):
  name=x['name'] if x['name'].startswith('PCA_') else 'PCA_'+x['name'];p=E/name
  raw=lzma.decompress(base64.b64decode(x['data']));assert sha(raw)==x['sha256']
  if p.suffix=='.json':p.write_bytes(raw)
  else:p.with_name(p.name+'.xz').write_bytes(base64.b64decode(x['data']));p.with_name(p.name+'.sha256').write_text(x['sha256']+'\n')
 assert r['exit_status']==0,(mode,'Audit incomplete; no unchanged rerun')
print('Focused intermediate gate finished: combined import, same-binary eight fixtures, raw ax2 and coherence scan; no Pool promotion.')
