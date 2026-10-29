"""Resolve endpoint project closure under EJR/(h''); verify all replay external objects under (h4)."""
from pathlib import Path
import json,subprocess,hashlib,re,shlex,sys
R=Path(__file__).resolve().parents[2];E=R/'evidence/pv-l1d-20261029';host='dombarker@100.108.41.90'
batch=subprocess.Popen(['git','cat-file','--batch'],cwd=R,stdin=subprocess.PIPE,stdout=subprocess.PIPE)
def git(s):
 batch.stdin.write((s+'\n').encode());batch.stdin.flush()
 line=batch.stdout.readline().decode().strip();parts=line.split()
 if len(parts)<3:raise RuntimeError(line)
 b=batch.stdout.read(int(parts[-1]));assert batch.stdout.read(1)==b'\n';return b
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
head=subprocess.check_output(['git','rev-parse','HEAD'],text=True).strip()
explicit=json.loads((R/'tools/pv-runjoin31-20261028/h5-explicit-sources.json').read_text())
tracked=subprocess.check_output(['git','ls-tree','-r','--name-only',head],text=True).splitlines()
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
 if m.startswith("XR") or m.split(".")[-1].startswith("XR"): raise RuntimeError("Ruling q forbidden import: "+m)
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
 else:
  suffix=m.replace('.','/')+'.lean'
  ps=[explicit[m]['path']] if m in explicit else [p for p in tracked if p.endswith('/lean/'+suffix)]
  if m in explicit:
   assert ps[0] in tracked
   assert hashlib.sha256(git(head+':'+ps[0])).hexdigest()==explicit[m]['sha256'],m
  if not ps:ps=[p for p in tracked if p.endswith('/'+suffix) or p.endswith('/'+m+'.lean.txt') or p.endswith('/'+m+'.lean')]
  if not ps and m.split('.')[-1] not in ['Funs','Types']:
   ps=[p for p in tracked if p.endswith('/'+m.split('.')[-1]+'.lean')]
  if not ps:ps=[p for p in tracked if p.endswith('/'+suffix+'.txt')]
  if not ps:
   ps=[p for p in tracked if p.endswith('/'+m.split('.')[-1]+'.lean.txt') and ('namespace '+m) in git(head+':'+p).decode()]
  if not ps:missing.add(m);return
  variants={hashlib.sha256(git(head+':'+p)).hexdigest() for p in ps}
  if len(variants)!=1:missing.add(m+' [conflicting h5 tracked variants]');return
  p=ps[0];b=git(head+':'+p);expected=hashlib.sha256(b).hexdigest()
  r=dict(path=p,git_blob=hashlib.sha1(b'blob '+str(len(b)).encode()+b'\0'+b).hexdigest());a='h5 own git-tracked HEAD'

 assert hashlib.sha256(b).hexdigest()==expected,m
 imports=re.findall(r'^(?:public )?import\s+(\S+)',uncomment(b.decode()),re.M)
 conflicts=[]
 if a != 'h5 own git-tracked HEAD':
  for p in tracked:
   if p.endswith('/lean/'+m.replace('.','/')+'.lean'):
    tb=git(head+':'+p);th=hashlib.sha256(tb).hexdigest()
    if th!=expected:conflicts.append(dict(path=p,sha256=th,selected_sha256=expected,ruling='h5 precedence amended by h5 prime'))
 done[m]=dict(tracked_conflicts=conflicts,authority=a,path=r['path'],git_blob=r.get('git_blob',r.get('blob')),sha256=expected,imports=imports);sources[m]=b.decode()
 for dep in imports:visit(dep)

roots=sys.argv[1:] or ['R1Z.PV_RunJoin_NativeFibre21']
label='admission-audit' if not sys.argv[1:] else 'focused'
for m in roots:visit(m)
(E/(label+'-resolution.json')).write_text(json.dumps(dict(head=head,research_revision=rev,resolved=done,unpinned=sorted(missing)),indent=2)+'\n')
(E/(label+'-project-sources.json')).write_text(json.dumps(sources)+'\n')
print('Project',len(sources),'h5',sum(r['authority'].startswith('h5') for r in done.values()),'missing',sorted(missing))
