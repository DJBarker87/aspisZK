from pathlib import Path
import subprocess,json,hashlib,re
D=Path(__file__).parent
runs=[(60300,'V181','5428621e2e'),(60301,'V178','5428621e2e'),(60302,'V178','0818b83e7a'),(60397,'Audit','ef2147b594')]
sha=lambda b:hashlib.sha256(b).hexdigest()
def timing(p):
 s=p.read_text()
 def val(k):return next(x.split(': ',1)[1].strip() for x in s.splitlines() if k in x)
 return dict(wall=val('Elapsed (wall clock)'),peak_rss_kib=int(val('Maximum resident set size')),swap=int(val('Swaps:')),exit=int(val('Exit status:')))
receipts=[]
for i,name,rev in runs:
 rev=subprocess.check_output(['git','rev-parse',rev],text=True).strip()
 p=f'docs/research/v8-r0-zk-20261009/lean/R1Z/PV_RDEA_{name}.lean'
 src=subprocess.check_output(['git','show',f'{rev}:{p}'])
 out=(D/f'out-{i}.log').read_text(); axioms=[s for s in out.splitlines() if 'depends on axioms:' in s or 'does not depend on any axioms' in s]
 r=dict(attempt=i,target='R1Z/PV_RDEA_'+name,command=f'run-joint.sh {i} R1Z/PV_RDEA_{name} J 7000 8',source_revision=rev,source_path=p,source_sha256=sha(src),source_blob=subprocess.check_output(['git','rev-parse',f'{rev}:{p}'],text=True).strip(),**timing(D/f'time-{i}.log'),print_axioms=axioms,credited=i!=60301,dependencies='project-pins.json plus preflight.json complete 5682 source/object checks; audit additionally imports exact successful V181/V178 objects',scope='MemoryHigh6G MemoryMax8G MemorySwapMax0 TasksMax64; Lean -M7000',error=[s for s in out.splitlines() if 'error:' in s])
 (D/f'{i}-receipt.json').write_text(json.dumps(r,indent=2)+'\n');receipts.append(r)
native=dict(target='native.py: reachable-oom.rs native and old-reference with failing allocator',source_revision=subprocess.check_output(['git','rev-parse','ef2147b594'],text=True).strip(),**timing(D/'native01-time.log'),print_axioms='N/A: finite native validation, no theorem',scope='MemoryHigh6G MemoryMax8G MemorySwapMax0 TasksMax64; optimized rustc1.94.1 std-only fixture',configuration='reachable-oom.json',binary_before_cleanup=dict(sha256='664901a4ff43a5b2a9c53f1a3a3ac70da13a9906d255b0b8157cc398f774b1ee',bytes=3957080,removed=True))
(D/'native01-receipt.json').write_text(json.dumps(native,indent=2)+'\n')
(D/'audit.json').write_text(json.dumps(dict(lean_attempts=4,native_scopes=1,kani=0,restored_rows=[],suspended_rows=['V181','V178'],axioms_audit=60397,focused_replay_restored_rows='empty: no restored rows; both new local proof modules compiled and imported once in combined audit',failed_attempts=[60301],no_new_trust=True,receipts=receipts,native=native),indent=2)+'\n')
print(json.dumps(dict(lean=4,native=1,peak=max(r['peak_rss_kib'] for r in receipts),native_receipt=native)))
