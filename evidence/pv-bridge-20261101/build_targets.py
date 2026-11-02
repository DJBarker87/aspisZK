"""Feed named proof targets to the unchanged capped runner; stop at first failure."""
from pathlib import Path
import hashlib,json,re,subprocess,sys
B=Path(__file__).resolve().parent
root=str(B);freeze=json.loads((B/'SOURCE-FREEZE.json').read_text())
new={p[:-5] for p in freeze}
def sha(p):return hashlib.file_digest(p.open('rb'),'sha256').hexdigest()
def deps(m,seen=None):
 seen=set() if seen is None else seen
 for line in re.findall(r'^import ([^\n]+)',(B/(m+'.lean')).read_text(),re.M):
  for n in line.split():
   if n in new and n not in seen:seen.add(n);deps(n,seen)
 return seen
lp=root+'/objects:/home/dombarker/project-offloads/codex-pv-evhc2-20261029/objects:/home/dombarker/project-offloads/codex-cx-reconcile-cache-20261028/objects:/home/dombarker/.elan/toolchains/leanprover--lean4---v4.32.0/lib/lean'
for token in sys.argv[1:]:
 a,m=token.split(':',1);a=int(a);assert 78100<=a<=78199 and a!=78196
 src=m+'.lean';assert sha(B/src)==freeze[src]['sha256'],('source changed',m)
 selected={}
 for n in sorted(deps(m)):
  assert (B/'objects'/(n+'.olean')).exists(),('new dependency not built',m,n)
  for suffix in ['.olean','.olean.private','.olean.server','.ir','.ilean']:
   p=B/'objects'/(n+suffix)
   if p.exists():selected[n+suffix]={'path':str(p),'sha256':sha(p)}
 cfg={'kind':'lean','module':m,'attempt':f'lean-{a}','sources':[src],'env':{'LEAN_PATH':lp},'timeout':600,'command':['/home/dombarker/.elan/toolchains/leanprover--lean4---v4.32.0/bin/lake','env','lean','-j1','-M7000','-DElab.async=false','-o','objects/'+m+'.olean',src],'source_revision':(B/'CODE-REVISION.txt').read_text().strip(),'source_freeze':freeze[src],'deps_fingerprint':{'cohort_manifest_sha256':'f8ff7cfcc649f1b99a01b0703353d4856a472ac198884cb80b706863b9d07d65','native_verification':'native-78196','selected_objects':selected,'resolver':'own flat PV_BR_* root; unchanged original namespace resolution'},'expected_time':'focused Lean elaboration against verified cached objects; no dependency build'}
 p=B/f'attempt-{a}.json';assert not p.exists(),('config exists',a);p.write_text(json.dumps(cfg,indent=2)+'\n')
 r=subprocess.run([sys.executable,'launch.py',str(a),'lean'],cwd=B,stdout=subprocess.PIPE,stderr=subprocess.STDOUT)
 (B/f'launch-{a}.log').write_bytes(r.stdout)
 if r.returncode:
  print(r.stdout.decode(errors='replace')[-6000:],flush=True);raise SystemExit(r.returncode)
 log=(B/f'lean-{a}'/'stdout.log').read_text()
 reports=re.findall(r"'([^']+)' (depends on axioms: \[[^]]*\]|does not depend on any axioms)",log)
 for name,body in reports:
  axioms=set(body.split('[',1)[1].split(']',1)[0].replace(',',' ').split()) if '[' in body else set()
  assert axioms<={'propext','Classical.choice','Quot.sound'},(m,name,axioms)
 obj={str(p.relative_to(B)):sha(p) for p in (B/'objects').glob(m+'.olean*')}
 (B/f'lean-{a}'/'validation.json').write_text(json.dumps({'module':m,'status':'PASS','actual_print_axioms':reports,'objects':obj,'source_sha256':sha(B/src),'source_revision':cfg['source_revision']},indent=2)+'\n')
 receipt=json.loads((B/f'lean-{a}'/'receipt.json').read_text())
 print('TARGET_GREEN',a,m,receipt['wall_seconds'],receipt['peak_rss_kib'],flush=True)
