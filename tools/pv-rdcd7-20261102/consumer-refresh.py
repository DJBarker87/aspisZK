"""Read-only differential census for refs advanced since the original inventory."""
from pathlib import Path
import subprocess,json,hashlib,re,sys
R=Path(__file__).resolve().parents[2];E=R/'evidence/pv-rdcd7-20261102';label=sys.argv[1] if len(sys.argv)>1 else 'session2';assert re.fullmatch(r'session[0-9]+(?:-final)?',label);out=E/(label+'-census');out.mkdir(exist_ok=True)
def git(*a):return subprocess.check_output(['git',*a],cwd=R)
s=git('for-each-ref','--format=%(refname) %(objectname)','refs/heads','refs/remotes').decode();(E/('REFS-'+label+'.txt')).write_text(s)
refs=[l.split() for l in s.splitlines()]+[['HEAD',git('rev-parse','HEAD').decode().strip()]]
original=json.load(open(E/'CONSUMERS-census.json'));old={x['revision'] for x in original['results']};known={(x['path'],x['sha256']) for x in json.load(open(E/'CONSUMER-variants.json'))};byrev={}
for ref,rev in refs:
 if rev not in old:byrev.setdefault(rev,[]).append(ref)
results=[];variants=[]
for rev,names in byrev.items():
 q=subprocess.run(['git','grep','-n','-I','-E','PV_RDCD4_(BytesSource|SliceRange194)',rev,'--','*.lean','*.py','*.sh','*.rs'],cwd=R,capture_output=True);assert q.returncode in (0,1),q.stderr
 hits=q.stdout.decode();p=out/('grep-'+rev+'.txt');p.write_text(hits)
 paths={l[len(rev)+1:].split(':',1)[0] for l in hits.splitlines()}
 q=subprocess.run(['git','grep','-n','-E','^import R1Z\\.PV_',rev,'--','*.lean'],cwd=R,capture_output=True);assert q.returncode in (0,1)
 edges={}
 for line in q.stdout.decode().splitlines():
  path,ln,body=line[len(rev)+1:].split(':',2)
  if '/R1Z/' in path:edges.setdefault('R1Z.'+Path(path).stem,set()).update(re.findall(r'R1Z\.[A-Za-z0-9_]+',body))
 cone={'R1Z.PV_RDCD4_BytesSource','R1Z.PV_RDCD4_SliceRange194'}
 while True:
  n=len(cone);cone|={m for m,deps in edges.items() if deps&cone}
  if len(cone)==n:break
 if paths:
  paths|={'docs/research/v8-r0-zk-20261009/lean/'+m.replace('.','/')+'.lean' for m in cone}
  for path in sorted(paths):
   b=git('show',rev+':'+path);h=hashlib.sha256(b).hexdigest()
   if (path,h) not in known:
    variants.append(dict(path=path,sha256=h,revision=rev,refs=names,blob=git('rev-parse',rev+':'+path).decode().strip()))
 results.append(dict(revision=rev,refs=names,grep_file=str(p.relative_to(E)),grep_sha256=hashlib.sha256(hits.encode()).hexdigest(),files=sorted(paths),reverse_import_cone=sorted(cone)))
(E/('CONSUMERS-'+label+'-refresh.json')).write_text(json.dumps(dict(refs_count=len(refs),original_census='CONSUMERS-census.json',additional_revisions=len(byrev),results=results,new_variants=variants,complete=True),indent=2)+'\n')
print('Differential census complete:',len(byrev),'revisions;',len(variants),'new variants')
for x in variants:print(','.join(x['refs']),x['path'])
