"""Read-only receipt index, distinguishing final rusage and observed cgroup peak."""
from pathlib import Path
import json,re
root=Path(__file__).resolve().parents[2];ev=root/'evidence/pv-cb-20261026'
lean=[]
for p in sorted(ev.glob('*.json')):
 if not p.stem.isdigit() or not 41200 <= int(p.stem) <= 41499:continue
 r=json.loads(p.read_text())
 if 'module' not in r or 'exit' not in r:continue
 if r['exit']==0:
  for line in r.get('axioms',[]):
   assert 'sorryAx' not in line,line
   m=re.search(r'axioms: \[([^\]]*)\]',line,re.S)
   if m:assert {x.strip() for x in m[1].split(',')} <= {'propext','Classical.choice','Quot.sound'},line
 lean.append({k:r.get(k) for k in ['attempt','module','exit','wall','peak_rss_kib','swap','source_revision','source_sha256','axioms','limits']})
assert len(lean)==100
native=[]
for p in sorted(ev.glob('*/collected-receipt.json')):
 if 'resume5' not in p.parent.name:continue
 r=json.loads(p.read_text());target_path=p.parent/'target.json'
 if target_path.exists():r.update(json.loads(target_path.read_text()))
 sample_path=p.parent/'cgroup-sample.json';sample=json.loads(sample_path.read_text()) if sample_path.exists() else None
 native.append(dict(name=p.parent.name,charged=r.get('attempt_charged',False),target=r.get('target'),exit=r.get('exit'),wall=r.get('wall'),gnu_time_peak_rss_kib=r.get('peak_rss_kib'),gnu_time_swap=r.get('swap'),source_revision=r.get('source_revision'),print_axioms=r.get('print_axioms'),limits=r.get('limits'),harness=r.get('harness'),unwind=r.get('unwind_bound'),timeout=r.get('timeout_seconds'),sampled_cgroup_observation=sample,receipt=str(p.relative_to(root))))
r=dict(source_identity='Revision plus exact source/proof-input hashes and retained per-attempt snapshots; some focused sources were uncommitted at measurement time. Not a claim that the revision alone reproduces the working source.',metric_policy='Native timeout GNU RSS is wrapper rusage, not aggregate peak; sampled cgroup memory.peak is reported separately, never substituted for an unobserved final peak. No sample means unavailable.',lean=lean,native=native)
(ev/'RESUME5-RECEIPTS-INDEX.json').write_text(json.dumps(r,indent=2)+'\n')
print('Indexed',len(lean),'Lean receipts;',len(native),'native attempts/refusals; accepted axiom allowlist PASS')
