"""Serial private rebuild of missing unchanged imports; no shared file writes."""
from pathlib import Path
import subprocess,json,re,hashlib,sys
E=Path(__file__).resolve().parent
base=json.loads((E/'NBX_DEPENDENCY_FIq_Install.json').read_text())
# Only existing source paths. No generated replacement, dictionary, source edit or new proof.
sources={}
for d in ['docs/research/100bit-spend-path-20261013/lean','lean']:
 for p in Path(d).glob('*.lean'):sources[p.stem]=p
for p in Path('lean/WAdm_Fissioned').glob('*.lean'):sources['WAdm_Fissioned.'+p.stem]=p
for d in ['bridge-typedfull-current-20261017','bridge-selected-current-20261018']:
 for p in Path('docs/research/100bit-spend-path-20261013/lean',d).glob('*.lean'):sources.setdefault(p.stem,p)
for group in ['AspisR1CircleSampleWrapper','AspisR1CircleFallback']:
 for p in (E/'NBX_imports'/group).glob('*.lean'):sources[group+'.'+p.stem]=p
sources.update({
 'AspisR1RowShape.Funs':Path('evidence/parse-sem-20261025/PSem-018/sources/AspisR1RowShape/Funs.lean'),
 'ExtractedSourceSemanticSampler':Path('docs/research/100bit-spend-path-20261013/lean/bridge-selected-current-20261018/ExtractedSourceSemanticSampler.lean'),
 'ExtractedSourceFull25Typed':Path('docs/research/100bit-spend-path-20261013/lean/bridge-typedfull-current-20261017/ExtractedSourceFull25Typed.lean'),
})
for p in Path('docs/research/100bit-spend-path-20261013/lean-candidates/current-circle-wrapper-20261019').glob('*.lean'):sources['AspisR1CircleSampleWrapper.'+p.stem]=p
# Query only resolution; the existing launchers still own each compile/scope.
import shlex
code="""from pathlib import Path
import json
roots=[Path('/home/dombarker/project-offloads/codex-cx-tx2codec-cache-20261028'),Path('/home/dombarker/project-offloads/codex-cx-sound-int2-20261025'),Path('/home/dombarker/project-offloads/codex-cx-sound-int2-20261025/objects'),Path('/home/dombarker/.elan/toolchains/leanprover--lean4---v4.32.0/lib/lean')]
names=set()
for r in roots:
 for p in (r.glob('*.olean') if r.name=='codex-cx-sound-int2-20261025' else r.rglob('*.olean')):names.add(str(p.relative_to(r).with_suffix('')).replace('/','.'))
print(json.dumps(sorted(names)))
"""
r=subprocess.run(['ssh','-o','ConnectTimeout=15','dombarker@100.108.41.90','python3 -c '+shlex.quote(code)],text=True,capture_output=True);assert r.returncode==0,r.stderr
available=set(json.loads(r.stdout));visiting=set();charged=len(list(E.glob('NBX_L*/receipt.json')))
def build(n):
 global charged
 if n in available:return
 assert n not in visiting,('cycle',n)
 assert n in sources,('STOP missing unchanged source',n)
 p=sources[n];visiting.add(n)
 for dep in re.findall(r'^import (\S+)',p.read_text(),re.M):build(dep)
 while True:
  charged+=1;assert charged<=115,'STOP reserve slots for remaining own roots'
  a=f'NBX_L{charged:03}'
  assert not (E/a).exists(),a
  with (E/'NBX_DEPENDENCY_ATTEMPTS.jsonl').open('a') as f:f.write(json.dumps(dict(attempt=a,module=n,path=str(p),sha256=hashlib.sha256(p.read_bytes()).hexdigest(),unchanged=True))+'\n')
  r=subprocess.run(['python3',str(E/'NBX_build.py'),a,str(p),n],capture_output=True,text=True)
  (E/(a+'-driver.log')).write_text(r.stdout+r.stderr)
  q=E/a/'receipt.json';assert q.exists(),('STOP own dependency launch failed',a,r.stdout,r.stderr)
  rc=json.loads(q.read_text());print(a,n,rc['exit_status'],rc['wall_seconds'],flush=True)
  if rc['exit_status']==0:available.add(n);break
  out=(E/a/'stdout.log').read_text()
  m=re.search("unknown module prefix '([^']+)'",out)
  if m:
   assert m.group(1) not in available,('inconsistent resolution',m.group(1))
   build(m.group(1))
   # Fresh transitive dependency input, not an unchanged timeout/kill rerun.
   continue
  raise SystemExit('STOP unchanged dependency failed; do not repair proved source '+a+' '+n+'\n'+out[-4000:])
 visiting.remove(n)
target=sys.argv[1] if len(sys.argv)>1 else 'RawTx1DigestLog'
if target in ['ALL_FIQ','ALL_IDA']:
 inventory=base if target=='ALL_FIQ' else json.loads((E/'NBX_DEPENDENCY_INVENTORY.json').read_text())
 for item in inventory['missing']:build(item['module'])
else:build(target)
# The exact local installation root may expose additional missing imports later.
print('COMPLETE',target,flush=True)
