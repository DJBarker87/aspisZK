from pathlib import Path
import subprocess,json,hashlib,sys,re
R=Path(__file__).resolve().parents[2];E=R/'evidence/pv-rdcd4-20261029';D='/home/dombarker/project-offloads/codex-pv-rdcd3-20261028/rdcd4-20261029';H='dombarker@100.108.41.90'
n=int(sys.argv[1]);m=sys.argv[2];assert 66300<=n<=66399
p=R/'docs/research/v8-r0-zk-20261009/lean'/(m+'.lean')
if not p.exists():p=R/'docs/research/100bit-spend-path-20261013/lean/prover-rw-20261023'/(m.split('/')[-1]+'.lean')
s=p.read_bytes()
# Do not resubmit an unchanged failed source under a different attempt ID.
for prior in E.glob('lean-*/receipt.json'):
 old=json.loads(prior.read_text())
 if old.get('module')==m and old.get('exit')!=0:
  assert old.get('source_sha256')!=hashlib.sha256(s).hexdigest(), 'unchanged failed source: edit/split before submission'
assert s==subprocess.check_output(['git','show','HEAD:'+str(p.relative_to(R))])
meta=dict(attempt=n,module=m,source_path=str(p.relative_to(R)),source_sha256=hashlib.sha256(s).hexdigest(),source_blob=subprocess.check_output(['git','rev-parse','HEAD:'+str(p.relative_to(R))],text=True).strip(),source_revision=subprocess.check_output(['git','rev-parse','HEAD'],text=True).strip(),authority='own tracked h5 project dependency or new PV_RDCD4 module; external closure preflight 5673 objects')
# Check the ID column, not substrings inside object hashes.
code='''from pathlib import Path
import json,re
n=ID
s=Path('/home/dombarker/project-offloads/r1-privacy-build-integration-20261019/evidence/sent.txt').read_text()
a=[l for l in s.splitlines() if len(l.split())>=3 and l.split()[2]==str(n)]
b=[str(p) for d in Path('/home/dombarker/project-offloads').glob('codex-pv-*') for p in d.glob('**/*'+str(n)+'*') if (p.is_file() or p.is_dir()) and d.name!='codex-pv-rdcd4-20261029' and not str(p).startswith('/home/dombarker/project-offloads/codex-pv-rdcd3-20261028/rdcd4-20261029/') and re.search(r'(?<![0-9a-fA-F])'+str(n)+r'(?![0-9a-fA-F])',p.name)]
print(json.dumps(dict(shared=a,private=b)))
assert not a and not b,(a,b)
'''.replace('ID',str(n))
r=subprocess.run(['ssh',H,'python3','-'],input=code,text=True,capture_output=True);(E/f'{n}-id-check.json').write_text(json.dumps(dict(exit=r.returncode,stdout=r.stdout,stderr=r.stderr),indent=2));assert r.returncode==0,r.stderr
# Diagnose admission before source transport (local-lean rule7). The scoped
# launch still performs its own reservation and same-command barrier later.
import shlex
out=E/('lean-'+str(n));out.mkdir(exist_ok=True)
G='/home/dombarker/project-offloads/codex-cx-prover-rw-20261023/src/tools/prover-rw-20261023/native-entropy'
remote=D+'/lean-'+str(n)
command='mkdir -p '+shlex.quote(remote)+'; python3 '+shlex.quote(G+'/reservation.py')+' '+shlex.quote(remote+'/admission-before-upload.json')+' > '+shlex.quote(remote+'/reservation-before-upload.log')+' 2>&1'
a=subprocess.run(['ssh',H,command],capture_output=True,text=True)
for name in ['admission-before-upload.json','reservation-before-upload.log']:
 q=subprocess.run(['ssh',H,'cat '+shlex.quote(remote+'/'+name)],capture_output=True,text=True)
 assert q.returncode==0,('pre-upload admission receipt missing',q.stderr)
 (out/name).write_text(q.stdout)
ad=json.load(open(out/'admission-before-upload.json'))
with (out/'admission-history.jsonl').open('a') as hist:hist.write(json.dumps(dict(exit=a.returncode,admission=ad,stage='before-source-upload'))+'\n')
if a.returncode!=0 or ad.get('allowed') is not True:
 print('UNCHARGED pre-upload admission refusal; no source transport or compiler launched',flush=True)
 if ad.get('error'):
  race=bool(re.search(r'\[Errno (?:2|19)\]',ad['error']));consecutive=0
  for line in reversed((out/'admission-history.jsonl').read_text().splitlines()):
   error=json.loads(line).get('admission',{}).get('error','')
   if re.search(r'\[Errno (?:2|19)\]',error):consecutive+=1
   else:break
  sys.exit(79 if race and consecutive<4 else 70)
 sys.exit(78)
subprocess.run(['scp','-q',str(p),H+':'+D+'/lean-sources/'+m+'.lean'],check=True)
# Capture actual private dependency objects before submission. Earlier receipts
# retain their original fields; final closure verification is separately labelled.
code = """from pathlib import Path
import json,hashlib,re
D=Path('/home/dombarker/project-offloads/codex-pv-rdcd3-20261028/rdcd4-20261029')
env=json.load(open(D/'env-J.json'));roots=[Path(x) for x in env['LEAN_PATH'].split(':')];seen={}
def go(module):
 if module in seen:return
 obj=next((r/(module+'.olean') for r in roots if (r/(module+'.olean')).exists()),None)
 source=D/'lean-sources'/(module+'.lean')
 seen[module]=dict(object_path=str(obj),object_sha256=hashlib.sha256(obj.read_bytes()).hexdigest() if obj else None)
 if source.exists() and module.startswith('R1Z/'):
  seen[module]['source_sha256']=hashlib.sha256(source.read_bytes()).hexdigest()
  deps=re.findall(r'^import\\s+(\\S+)',source.read_text(),re.M);seen[module]['imports']=[x.replace('.','/') for x in deps]
  for dep in seen[module]['imports']:go(dep)
source=D/'lean-sources'/(MODULE+'.lean')
imports=re.findall(r'^import\\s+(\\S+)',source.read_text(),re.M)
for dep in imports:go(dep.replace('.','/'))
print(json.dumps(dict(module=MODULE,environment=env,objects=seen,external_manifest_sha256=hashlib.sha256((D/'external-object-manifest.json').read_bytes()).hexdigest()),sort_keys=True))
""".replace('MODULE',repr(m))
r=subprocess.run(['ssh',H,'python3','-'],input=code,text=True,capture_output=True)
assert r.returncode==0,r.stderr
deps=json.loads(r.stdout);assert deps['objects'],deps
(E/f'{n}-dependencies.json').write_text(json.dumps(deps,indent=2)+'\n')
meta['dependencies_sha256']=hashlib.sha256((E/f'{n}-dependencies.json').read_bytes()).hexdigest()
meta['dependencies_snapshot']=f'{n}-dependencies.json'
(E/f'{n}-source.json').write_text(json.dumps(meta,indent=2)+'\n')
c=['timeout','900','python3','/home/dombarker/project-offloads/aspis-fs-generic-20261006/evidence/run2.py',D+'/env-J.json',D+'/lean-objects',D+'/lean-sources',D+'/lean-objects/'+m+'.olean',D+'/lean-sources/'+m+'.lean','7000']
r=subprocess.run([sys.executable,str(R/'tools/pv-rdcd4-20261029/scope.py'),'lean-'+str(n),'Lean',*c])
p=E/('lean-'+str(n))/'receipt.json'
if p.exists():j=json.loads(p.read_text());j.update(meta);p.write_text(json.dumps(j,indent=2)+'\n')
sys.exit(r.returncode)
