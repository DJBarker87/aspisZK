#!/usr/bin/env python3
"""Recover the finite missing mask proof DAG; never build or change proofs."""
from pathlib import Path
import re,json,hashlib,sys
R=Path(__file__).resolve().parents[2];B=R/'docs/research/100bit-spend-path-20261013';T=Path(__file__).parent;S=B/'lean-candidates/s1-mask-support-20261025';pin=T/'support-binding.json';sha=lambda p:hashlib.sha256(p.read_bytes()).hexdigest()
if '--check' in sys.argv:
 j=json.loads(pin.read_text())
 for row in j['targets']:
  p=R/row['original'];q=R/row['maintained'];assert sha(p)==row['original_sha256'];s=re.sub(r'^set_option (maxHeartbeats|maxRecDepth) [0-9]+\n','',p.read_text(),flags=re.M);assert q.read_text()==s and sha(q)==row['maintained_sha256']
 print('PASS exact',len(j['targets']),'source copies; only heartbeat/depth overrides removed; no compiler')
 raise SystemExit
assert not S.exists() and not pin.exists();S.mkdir();paths=['/tmp/s126-current-caller-20261021-objects',*Path('/tmp/s126-s6-sdk-first-path-20261024.txt').read_text().strip().split(':')];seen=set();rows=[]
def walk(n):
 if n in seen:return
 seen.add(n)
 if any((Path(p)/(n.replace('.','/')+'.olean')).is_file()for p in paths):return
 p=B/'lean'/(n.replace('.','/')+'.lean');assert p.is_file(),n;s=p.read_text();assert not re.search(r'(?m)^\s*axiom\b|\b(sorry|native_decide|bv_decide)\b',s),n
 imports=re.findall(r'^import ([A-Za-z0-9_.]+)',s,re.M)
 for dep in imports:walk(dep)
 q=S/(n.replace('.','/')+'.lean');q.parent.mkdir(exist_ok=True,parents=True);q.write_text(re.sub(r'^set_option (maxHeartbeats|maxRecDepth) [0-9]+\n','',s,flags=re.M));rows.append(dict(module=n,original=str(p.relative_to(R)),original_sha256=sha(p),maintained=str(q.relative_to(R)),maintained_sha256=sha(q),imports=imports))
walk('ExtractedMaskCallerModel');pin.write_text(json.dumps(dict(schema='focused-extractor-proof-packet-v1',status='PREPARED_SOURCE_ONLY',reason='24 project proof objects absent from the current pinned warm path; reuse their mathematical proofs under current exact imports rather than reprove them; not a cold library/package build',consumer='S1 actual reached mask canonical output and final arithmetic domain discharge',targets=rows),indent=2)+'\n');print('PREPARED',len(rows),'missing proof targets')
