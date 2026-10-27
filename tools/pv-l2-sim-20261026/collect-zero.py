from pathlib import Path
import hashlib,json,re,shlex,subprocess
R=Path(__file__).resolve().parents[2];E=R/'evidence/pv-l2-sim-20261026'
H='dombarker@100.108.41.90';D='/home/dombarker/project-offloads/codex-pv-l2-sim-20261026'
names=['m31_zero','m31_zero','m31_zero','cm31_zero','qm31_zero','wide_zero',
 'limbs_success','limbs_complete','limbs_success_pointwise','limbs_zero',
 'bytes_success','bytes_canonical','bytes_zero','wrong_length','reject_limb_0',
 'reject_limb_3','reject_limb_7','nonzero_limb','reject_limb_6','reject_limb_4']
paths={}
for i in range(1,21):
 z=f'z{i:02d}'
 paths[z]=[f'{kind}-{z}.{suffix}' for kind,suffix in
  [('out','log'),('time','log'),('exit','txt'),('reservation','json')]]
code='from pathlib import Path;import json;d=Path('+repr(D)+');print(json.dumps({k:{p:(d/p).read_text() for p in ps if (d/p).exists()} for k,ps in '+repr(paths)+'.items()}))'
raw=json.loads(subprocess.check_output(['ssh',H,'python3 -c '+shlex.quote(code)],text=True))
rev=subprocess.check_output(['git','rev-parse','HEAD'],text=True).strip()
for i,name in enumerate(names,1):
 z=f'z{i:02d}';p=E/z;p.mkdir(exist_ok=True)
 for filename,contents in raw[z].items():(p/filename.split('-')[0].replace('.txt','')).with_suffix('.log' if not filename.endswith('.json') else '.json').write_text(contents)
 src=E/'z02/source.rs' if i<=2 else E/'z07/source.rs' if i<=8 else R/'tools/pv-l2-sim-20261026/PV_L2_Zero_native.rs'
 tm=raw[z][f'time-{z}.log'];out=raw[z][f'out-{z}.log'];status=int(raw[z][f'exit-{z}.txt'])
 def metric(pattern):
  m=re.search(pattern,tm,re.M);return m[1] if m else None
 receipt=dict(attempt=z,target='PV_L2_zero::'+name,source_revision=rev,
  source_sha256=hashlib.sha256(src.read_bytes()).hexdigest(),
  source_snapshot=str(src.relative_to(R)),binding='tools/pv-l2-sim-20261026/zero-source-binding.json',
  dependency_fingerprint='Kani 0.67.0 standalone bundled sysroot',exit=status,
  wall=metric(r'Elapsed.*: (\S+)\s*$'),peak_rss_kib=int(metric(r'Maximum resident.*: (\d+)') or 0),
  swaps=int(metric(r'Swaps: (\d+)') or 0),print_axioms='N/A: Kani',
  scope=dict(MemoryHigh='6G',MemoryMax='8G',MemorySwapMax=0,TasksMax=64),
  result='passed' if status==0 else 'CLI rejection' if i==1 else 'source assembly rejection' if i==2 else 'memcmp unwind failure',
  stubs=False,expected_work='Kani code generation then bounded source predicate/decoder verification; no arithmetic elimination')
 (p/'receipt.json').write_text(json.dumps(receipt,indent=2)+'\n')
 print(z,name,status)
