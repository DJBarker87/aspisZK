"""D513 private plain-copy overlay and first-root preflight; no compiler."""
from pathlib import Path
import json, hashlib, shutil, time, re, os
B=Path(__file__).resolve().parent; E=B/'resume3'; E.mkdir(exist_ok=True)
sha=lambda p:hashlib.sha256(Path(p).read_bytes()).hexdigest()
plan=json.load(open(B/'plan.json')); pins=json.load(open(B/'NDR_FINAL_COHORT_PINS.json'))
N=B.parent/'codex-cx-reconcile-cache-20261028/objects'
roots=[B/'objects',N,Path('/home/dombarker/.elan/toolchains/leanprover--lean4---v4.32.0/lib/lean')]
def resolve(m):
 top=m.split('.')[0]
 root=next(r for r in roots if (r/top).is_dir() or (r/(top+'.olean')).is_file())
 return root/(m.replace('.','/')+'.olean')
def companions(p):
 return [q for q in [p,Path(str(p)+'.server'),Path(str(p)+'.private'),p.with_suffix('.ir')] if q.is_file()]
def copy(src,dst):
 dst.parent.mkdir(parents=True,exist_ok=True)
 assert not dst.is_symlink()
 if not dst.exists() or sha(dst)!=sha(src):shutil.copyfile(src,dst)
 assert sha(src)==sha(dst)
 assert not dst.is_symlink() and dst.stat().st_nlink==1
 return dict(source=str(src),path=str(dst),sha256=sha(dst),bytes=dst.stat().st_size)
start=time.monotonic(); ndr={v['module']:dict(path=v['object_path'],sha256=v['object_sha256'],kind='authoritative NDR') for v in pins['entries']}
output=json.load(open(B/'NDR_FINAL_OUTPUT_PINS.json'))
ndr['NDR_CombinedAudit']=dict(path=str(N/'NDR_CombinedAudit.olean'),sha256=output['objects/NDR_CombinedAudit.olean']['sha256'],kind='authoritative NDR output')
rows=dict(ndr)
for m in plan['rebuild']+plan['reuse']:
 assert m not in rows
 v=plan['events'][m];rows[m]=dict(path=v['path'],sha256=v['sha256'],kind='pending rebuild' if m in plan['rebuild'] else 'fingerprint-checked event reuse')
# Mathlib.Data.FinEnum is absent from NDR, so the closure needs a complete
# private Mathlib namespace. This is necessary staging, not optional reuse.
required={m.split('.')[0] for m in plan['rebuild']}
for m in plan['reuse']:
 if not (N/(m.replace('.','/')+'.olean')).exists():required.add(m.split('.')[0])
copies=[];effective=[]
for m,v in rows.items():
 src=Path(v['path']);assert sha(src)==v['sha256'],m
 if m.split('.')[0] in required:
  dst=roots[0]/(m.replace('.','/')+'.olean')
  for q in companions(src):
   target=dst.with_suffix('.ir') if q.suffix=='.ir' else Path(str(dst)+str(q)[len(str(src)):])
   copies.append(copy(q,target))
for m,v in rows.items():
 p=resolve(m);assert p.is_file(),(m,str(p))
 assert sha(p)==v['sha256'],(m,str(p),'effective hash mismatch')
 effective.append(dict(module=m,path=str(p),sha256=sha(p),kind=v['kind'],companions=[dict(path=str(q),sha256=sha(q),bytes=q.stat().st_size) for q in companions(p) if q!=p]))
# Check every edge, including all pending rebuild imports, against this inventory.
for m,ds in plan['full_graph'].items():
 if m not in rows:continue
 for d in ds:assert d in rows,(m,d,'closure gap')
# Rebuilds may never read pending rebuild slots; verify order before compile.
done=set(ndr)|set(plan['reuse'])
for m in plan['rebuild']:
 assert set(plan['edges'][m])<=done,(m,sorted(set(plan['edges'][m])-done))
 done.add(m)
for m in plan['rebuild']:
 p=B/'sources'/(m.replace('.','/')+'.lean');assert sha(p)==plan['sources'][m]['sha256']
assert len(plan['rebuild'])==510
# Independently recheck IDs across job receipt/output trees; no source cache scan.
used={};pat=re.compile(r'(?<![0-9])(7[01][0-9]{3})(?![0-9])')
for job in B.parent.glob('codex-*'):
 candidates=list(job.glob('*'))
 if (job/'evidence').exists():candidates+=list((job/'evidence').rglob('*'))
 for q in job.glob('lean-*'):
  if q.is_dir():candidates+=list(q.glob('*'))
 for p in candidates:
  if p.is_dir() or not any(t in p.name for t in ['receipt','submission','attempt','modules-','out-','lean-','admission','time-']):continue
  for a in pat.findall(str(p.relative_to(job))):used.setdefault(a,[]).append(str(p))
sent=B.parent/'r1-privacy-build-integration-20261019/evidence/sent.txt'
if sent.exists():
 for line in sent.read_text().splitlines():
  for a in pat.findall(line):used.setdefault(a,[]).append('sent.txt: '+line)
(E/'id-audit.json').write_text(json.dumps(used,indent=2)+'\n')
result=dict(status='PASS',ruling='D513 h6 double-prime; D490 u-prime',source_revision='5098cacee75c803ba0486836a94c9894afbafab4',previous_failed_attempt=71000,next_attempt=71001,failure_class='pre-elaboration environment: first-root namespace shadowing',environment_diff='Complete private plain-copy namespace overlays replace the partial overlay. All 510 old event objects are verified staging slots and MUST be replaced topologically before any dependent consumes them. No authority directory is written.',Mathlib_reason='FinEnum is event-only and absent from authoritative NDR; complete private Mathlib is required to make that object reachable without mutating NDR. Every other Mathlib object remains an exact NDR plain copy.',LEAN_PATH=':'.join(map(str,roots)),required_private_namespaces=sorted(required),modules=len(effective),rebuilds=510,entries=effective,copies=copies,wall_seconds=time.monotonic()-start,cohort_manifest_sha256=sha(B/'NDR_FINAL_COHORT_PINS.json'),consumer_sha256=plan['consumer_sha256'])
(E/'first-root-preflight.json').write_text(json.dumps(result,indent=2)+'\n')
print(json.dumps({k:v for k,v in result.items() if k not in ['entries','copies','required_private_namespaces']}))
