"""Record tiny Std-only local checks; never launches a compiler or build."""
from pathlib import Path
import hashlib,json,re
r=Path(__file__).resolve().parents[3]
e=r/'docs/research/100bit-spend-path-20261013/evidence/prover-rw-20261023/success-p8/local'
tool=Path.home()/'.elan/toolchains/leanprover--lean4---v4.32.0'
project=r/'docs/research/100bit-spend-path-20261013/evidence/s2d-20261023'
sha=lambda p:hashlib.sha256(p.read_bytes()).hexdigest()
pins={str(p):sha(p) for p in [tool/'bin/lean',tool/'lib/lean/Std.olean',project/'lakefile.toml',project/'lean-toolchain']}
for name,module,status in [('pole-index-001','PV_PoleIndexBounds',0),('poly-index-001','PV_PolyIndexBounds',0),('countdown-001','PV_Countdown',0),('pole-partition-001','PV_PoleMaskPartition',0)]:
 log=e/(name+'.log')
 if not log.exists() or status is None:continue
 src=r/'docs/research/v8-r0-zk-20261009/lean/R1Z'/(module+'.lean')
 s=log.read_text();axioms=re.findall(r"'[^'\n]+' (?:depends on axioms: \[[\s\S]*?\]|does not depend on any axioms)",s)
 assert 'error:' not in s and 'sorryAx' not in s
 for a in axioms:
  if 'depends on axioms:' in a:assert set(x.strip() for x in a.split('depends on axioms: [')[1].split(']')[0].split(','))<={'propext','Classical.choice','Quot.sound'}
 snap=e/(name+'.lean.txt')
 if snap.exists():assert snap.read_bytes()==src.read_bytes()
 else:snap.write_bytes(src.read_bytes())
 rec=dict(attempt=name,module='R1Z/'+module,source_revision='3d2831d490+new-local-Std-only-module',source_sha256=sha(src),source_snapshot=snap.name,exit_status=status,wall_seconds=float(re.search(r'([\d.]+) real',s)[1]),peak_rss_bytes=int(re.search(r'(\d+)\s+maximum resident set size',s)[1]),swaps=int(re.search(r'(\d+)\s+swaps',s)[1]),print_axioms=axioms,command=['/usr/bin/time','-l','lake','env','lean','-M7000',str(src)],cwd=str(project),dependency_pins=pins,deps_fingerprint=hashlib.sha256(json.dumps(pins,sort_keys=True).encode()).hexdigest(),limits=dict(lean_memory_mb=7000),scope='Small local Std-only focused check, ordinary development machine, permitted by local-lean rule1/lead(c). No cgroup available on macOS; no cold dependency build. Std root/compiler pinned, not a complete transitive source/object release audit.')
 (e/(name+'-receipt.json')).write_text(json.dumps(rec,indent=2)+'\n')
 print(name,status,rec['wall_seconds'],rec['peak_rss_bytes'])
