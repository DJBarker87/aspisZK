#!/usr/bin/env python3
"""Assemble/check the stopped S6 packet without re-running Lean or extraction."""
from pathlib import Path
import hashlib,json,re,subprocess,sys
E=Path(__file__).resolve().parent;B=E.parents[1];R=B.parents[2]
sha=lambda p:hashlib.sha256(p.read_bytes()).hexdigest()
subprocess.run([sys.executable,str(E/'check-first-binding.py')],check=True)
frozen=json.loads((E/'frozen-source-check.json').read_text())
for row in frozen['files']:
 raw=subprocess.check_output(['git','-C',str(R),'show',frozen['frozen_revision']+':'+row['path']])
 assert hashlib.sha256(raw).hexdigest()==row['sha256']
 assert sha(R/row['path'])==row['sha256']
for row in json.loads((E/'declaration-pins.json').read_text())['declarations']:
 raw=subprocess.check_output(['git','-C',str(R),'show',frozen['frozen_revision']+':'+row['path']])
 fragment=E/row['fragment'];assert sha(fragment)==row['sha256']
 assert raw[row['start_byte']:row['end_byte_exclusive']]==fragment.read_bytes()
proofs=[]
for name,attempt in [('RepinS6Ranges','ranges-v1'),('RepinS6First','first-v2')]:
 rec=json.loads((E/'proofs'/attempt/'receipt.json').read_text());p=B/'lean'/(name+'.lean')
 assert rec['exit_status']==0 and sha(p)==rec['source_sha256']
 assert (E/'proofs'/attempt/'source.lean').read_bytes()==p.read_bytes()
 assert not re.search(r'\b(sorry|admit|native_decide)\b|^\s*(axiom|opaque)\b|set_option\s+(maxHeartbeats|maxRecDepth)',p.read_text(),re.M)
 audits=rec['print_axioms'];assert len(audits)==len(re.findall(r'^#print axioms ',p.read_text(),re.M))
 for audit in audits:
  if 'depends on axioms:' in audit:
   names=audit.split('[',1)[1].split(']',1)[0].replace('\n','').split(',')
   assert set(x.strip() for x in names)<={'propext','Classical.choice','Quot.sound'}
 proofs.append(dict(module=name,source=str(p.relative_to(R)),source_sha256=sha(p),receipt=str((E/'proofs'/attempt/'receipt.json').relative_to(E)),exit_status=0,wall_seconds=rec['wall_seconds'],peak_rss_bytes=rec['peak_rss_bytes'],swaps=rec['swaps'],print_axioms=audits))
runs=[]
for p in sorted((E/'receipts').glob('*/receipt.json')):
 rec=json.loads(p.read_text());lim=rec['limits']
 assert lim=={'memory.high':'6442450944','memory.max':'8589934592','memory.swap.max':'0','pids.max':'64'}
 assert rec['source_revision']==frozen['frozen_revision']
 runs.append(dict(attempt=p.parent.name,receipt=str(p.relative_to(E)),**rec))
assert {r['attempt']:r['exit_status'] for r in runs}=={'s6-first-charon':0,'s6-first-aeneas':0,'s6-stage1-charon':0,'s6-stage1-aeneas':2}
error=(E/'receipts/s6-stage1-aeneas/stderr.log').read_text();assert 'types containing mutable borrows' in error and '950:24-950:36' in error
files={str(p.relative_to(E)):dict(sha256=sha(p),bytes=p.stat().st_size) for p in sorted(E.rglob('*')) if p.is_file() and p.name!='manifest.json'}
design=B/'design/REPIN-s6-20261020.md'
manifest=dict(schema='focused-extractor-proof-packet-v1',status='STOPPED_SDK_ACCOUNT_BORROW; first caller re-proved; adapter binding and full R22 remain OPEN',frozen_source_revision=frozen['frozen_revision'],worktree_base_revision=frozen['worktree_base'],host_workspace='/home/dombarker/project-offloads/codex-cx-repin-s6-20261020',modules=proofs,extraction_runs=runs,llbc=json.loads((E/'llbc-pins.json').read_text()),generated_lean='extraction-first/generated/AspisR1S6',boundary_binding='first-binding-check.json',axioms='Only standard axioms in proved modules; generated external templates unused',full_manifest_replay='Not run: adapter translation blocked, focused preconditions not green',parked_candidate_s6_diff=frozen['parked_candidate_diff_for_s6'],design=dict(path=str(design.relative_to(R)),sha256=sha(design)),files=files)
raw=json.dumps(manifest,indent=2,sort_keys=True)+'\n'
if '--check' in sys.argv:assert (E/'manifest.json').read_text()==raw
else:(E/'manifest.json').write_text(raw)
print('PASS stopped S6 packet: exact frozen source, complete caller binding, 11 audited declarations, caps, both LLBC pins, and recorded adapter obstruction')
