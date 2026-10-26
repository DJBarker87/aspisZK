"""Read-only metric/axiom collection for a completed manual local invocation."""
from pathlib import Path
import hashlib,json,re,sys,subprocess
r=Path(__file__).resolve().parents[3];e=r/'evidence/pv-rw-step-20261026';d=e/'local';d.mkdir(exist_ok=True)
a=int(sys.argv[1]);module=sys.argv[2];status=int(sys.argv[3]);p=r/'docs/research/v8-r0-zk-20261009/lean/R1Z'/(module+'.lean');log=(e/f'local-{a}.log').read_text();ip=d/f'{a}-input.json';sha=lambda q:hashlib.sha256(q.read_bytes()).hexdigest()
if ip.exists():x=json.loads(ip.read_text());assert x['source_sha256']==sha(d/x['source_snapshot'])
else:
 snap=d/f'{a}.lean.txt'
 if not snap.exists():snap.write_bytes(p.read_bytes())
 x=dict(attempt=a,kind='local',module='R1Z/'+module,source_sha256=sha(snap),source_snapshot=snap.name,source_revision='09df2340e2+local-proof',note='Post-hoc receipt from retained exact source; invocation input was not separately pinned before launch.',command=['/usr/bin/time','-l','env','LEAN_PATH=/private/tmp/pv-rw-step-local-20261026','lake','env','lean','-M7000','-R',str(r/'docs/research/v8-r0-zk-20261009/lean'),'-o',f'/private/tmp/pv-rw-step-local-20261026/R1Z/{module}.olean',str(p)],cwd=str(r/'docs/research/100bit-spend-path-20261013/evidence/s2d-20261023'),limits=dict(lean_memory_mb=7000),scope='Tiny cached local Std-only job; no dependency build, no local cgroup; not a coherent release replay.')
if 'dependency_pins' not in x:
 tool=Path('/Users/dominic/.elan/toolchains/leanprover--lean4---v4.32.0');project=r/'docs/research/100bit-spend-path-20261013/evidence/s2d-20261023';cache=Path('/private/tmp/pv-rw-step-local-20261026')
 pins={str(q):sha(q) for q in [tool/'bin/lean',tool/'lib/lean/Std.olean',project/'lakefile.toml',project/'lean-toolchain']};seen=set()
 def visit(name):
  if name in seen or name=='Std':return
  seen.add(name);assert name.startswith('R1Z.PV_RW_')
  q=cache/(name.replace('.','/')+'.olean');assert q.is_file(),q
  pins[str(q)]=sha(q)
  source=r/'docs/research/v8-r0-zk-20261009/lean'/(name.replace('.','/')+'.lean')
  for child in re.findall(r'^import ([\w.]+)',source.read_text(),re.M):visit(child)
 for name in re.findall(r'^import ([\w.]+)',(d/x['source_snapshot']).read_text(),re.M):visit(name)
 x.update(dependency_pins=pins,deps_fingerprint=hashlib.sha256(json.dumps(pins,sort_keys=True).encode()).hexdigest())
reports=re.findall(r"'[^'\n]+' (?:depends on axioms: \[[\s\S]*?\]|does not depend on any axioms)",log)
x.update(exit_status=status,wall_seconds=float(re.search(r'([\d.]+) real',log)[1]),peak_rss_bytes=int(re.search(r'(\d+)\s+maximum resident set size',log)[1]),swaps=int(re.search(r'(\d+)\s+swaps',log)[1]),print_axioms=reports,log=f'../local-{a}.log')
if status==0:
 assert reports and 'error:' not in log and 'sorryAx' not in log
 for report in reports:
  if 'depends on axioms:' in report:assert set(v.strip() for v in report.split('depends on axioms: [')[1].split(']')[0].split(','))<={'propext','Classical.choice','Quot.sound'}
assert x['peak_rss_bytes']<8*2**30
(d/f'{a}-receipt.json').write_text(json.dumps(x,indent=2)+'\n');print(a,status,x['wall_seconds'],x['peak_rss_bytes'])
