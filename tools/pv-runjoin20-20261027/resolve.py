"""Resolve endpoint project closure under EJR/(h''); verify all replay external objects under (h4)."""
from pathlib import Path
import json,subprocess,hashlib,re,shlex
R=Path(__file__).resolve().parents[2];E=R/'evidence/pv-runjoin20-20261027';host='dombarker@100.108.41.90'
def git(s):return subprocess.check_output(['git','show',s],cwd=R)
rev=subprocess.check_output(['git','rev-parse','research'],text=True).strip()
ip='evidence/envj-rebuild-20261026/EJR_final-inventory.json';ep='evidence/pv-replay-20261027/receipts/external-object-manifest.json';fp='docs/research/100bit-spend-path-20261013/evidence/prover-commit47-20261022/final-source-freeze.json'
ib=git(rev+':'+ip);eb=git(rev+':'+ep);fb=git(rev+':'+fp)
inv=json.loads(ib);external={r['module'].replace('/','.'):r for r in json.loads(eb)};freeze=json.loads(fb)
plan=json.loads(git(rev+':evidence/pv-replay-20261027/replay-plan.json'))
replay={m.replace('/','.'):r for m,r in plan['nodes'].items()}
selected={}
for r in inv['selected']:
 if not r.get('resolution'):continue
 m=r['module'].replace('/','.')
 if m not in selected or (m in replay and r['sha256']==replay[m]['source_sha256']):selected[m]=r
frozen={r['module']:r for r in freeze['sources']}
mp='docs/research/100bit-spend-path-20261013/evidence/prover-commit15-20261021/manifest.json'
manifest15=json.loads(git(rev+':'+mp));frozen15={ 'R1Z.'+Path(p).stem:dict(path=p,sha256=h) for p,h in manifest15['sources'].items() if p.endswith('.lean') }
sp='docs/research/100bit-spend-path-20261013/evidence/prover-commit5-20261021/source-release.json'
sr5=json.loads(git(rev+':'+sp));frozen5={'R1Z.'+Path(p).stem:dict(path=p,sha256=h) for p,h in sr5['files'].items() if p.endswith('.lean')}
done={};missing=set();sources={}
ejs_path='evidence/envj-rebuild2-20261026/EJS_missing-payload.json'
ejs={r['module'].replace('/','.'):r for r in json.loads(git(rev+':'+ejs_path))['rows']}
def uncomment(s):
 depth=0;out=[];i=0
 while i<len(s):
  if s[i:i+2]=='/-':depth+=1;i+=2
  elif depth and s[i:i+2]=='-/':depth-=1;i+=2
  elif depth:out.append('\n' if s[i]=='\n' else ' ');i+=1
  elif s[i:i+2]=='--':
   j=s.find('\n',i);i=len(s) if j<0 else j
  else:out.append(s[i]);i+=1
 return ''.join(out)

def visit(m):
 if m in done or m in missing:return
 if m in external:done[m]=dict(authority=ep,**external[m]);return
 if m in selected:
  x=selected[m];r=x['resolution'];b=git(r['blob']);expected=x['sha256'];a=ip
 elif m in frozen5:
  r=frozen5[m];b=git(sr5['source_revision']+':'+r['path']);expected=r['sha256'];a=sp
 elif m in frozen15:
  r=frozen15[m];b=git(manifest15['source_revision_at_final_audit']+':'+r['path']);expected=r['sha256'];a=mp
 elif m in ejs:
  r=ejs[m];b=git(r['blob']);expected=r['source_sha256'];a=ejs_path
 elif m in frozen:
  r=frozen[m];b=git(freeze['revision']+':'+r['path']);expected=r['sha256'];a=fp
 else:missing.add(m);return
 assert hashlib.sha256(b).hexdigest()==expected,m
 imports=re.findall(r'^import\s+(\S+)',uncomment(b.decode()),re.M)
 done[m]=dict(authority=a,path=r['path'],sha256=expected,imports=imports);sources[m]=b.decode()
 for dep in imports:visit(dep)
visit('R1Z.PrivacyR1HeadlineDeployedReal')
visit('AspisR1ProducerRelease47.Funs')
(E/'external-object-manifest.json').write_bytes(eb)
payload=json.dumps(list(external.values()))
code="""import json,sys,hashlib,pathlib
rows=json.load(sys.stdin);out=[]
for r in rows:
 p=pathlib.Path(r['path']);actual=hashlib.sha256(p.read_bytes()).hexdigest() if p.is_file() else None
 out.append(dict(**r,actual_sha256=actual,match=actual==r['object_sha256']))
print(json.dumps(out))
"""
cache=E/'external-hash-check.json'
if cache.exists(): checks=json.loads(cache.read_text())
else:
 r=subprocess.run(['ssh',host,'python3 -c '+shlex.quote(code)],input=payload,text=True,capture_output=True);assert r.returncode==0,r.stderr
 checks=json.loads(r.stdout)
(E/'external-hash-check.json').write_text(json.dumps(checks,indent=2)+'\n')
out=dict(research_revision=rev,authorities={p:hashlib.sha256(b).hexdigest() for p,b in [(ip,ib),(ep,eb),(fp,fb)]},resolved=done,unpinned=sorted(missing),external_verified=len(checks),external_mismatches=[r for r in checks if not r['match']],endpoint_audit_rerun=False)
(E/'endpoint-resolution.json').write_text(json.dumps(out,indent=2)+'\n');(E/'project-sources.json').write_text(json.dumps(sources)+'\n')
print(json.dumps(dict(project_modules=len(sources),external_verified=len(checks),mismatches=len(out['external_mismatches']),unpinned=out['unpinned'])))
assert not missing and not out['external_mismatches']
