"""Collect immutable Lean receipts and verify final JGa sources and premise delta."""
from pathlib import Path
import hashlib,json,re,subprocess
P=Path(__file__).resolve().parent;R=P.parents[1]
def sha(p):return hashlib.sha256(p.read_bytes()).hexdigest()
receipts=[json.loads(p.read_text()) for p in sorted(P.glob('JGa14_*/receipt.json'))]
assert len(receipts)==100
assert [r['attempt'] for r in receipts]==[f'JGa14_{i:03}' for i in range(1,101)]
green={};failures=[]
for r in receipts:
 assert r['limits']=={'memory.high':'6442450944','memory.max':'8589934592','memory.swap.max':'0','pids.max':'64'}
 assert r['swaps']=='0'
 if r['exit_status']==0:
  assert all('sorryAx' not in a for a in r['print_axioms'])
  for n,h in r['source_hashes'].items():green[n]=dict(sha256=h,attempt=r['attempt'],axioms=r['print_axioms'])
 else:
  failures.append(dict(attempt=r['attempt'],source=r['sources'],exit=r['exit_status'],errors=(P/r['attempt']/'stdout.log').read_text()))
valid=[];unchecked=[]
for f in sorted((R/'lean').glob('JGa_*.lean')):
 info=green.get(f.name)
 if not info or info['sha256']!=sha(f):unchecked.append(str(f.relative_to(R)));continue
 assert not re.search(r'\b(sorry|admit|axiom|native_decide)\b|set_option\s+(maxRecDepth|maxHeartbeats)',f.read_text()),f
 valid.append(dict(source=str(f.relative_to(R)),**info))
assert not unchecked,unchecked
(P/'JGa_VALIDATION.json').write_text(json.dumps(valid,indent=2)+'\n')
(P/'JGa_FAILURES.json').write_text(json.dumps(failures,indent=2)+'\n')
with (P/'JGa_ATTEMPTS.jsonl').open('w') as out:
 for r in receipts:out.write(json.dumps(r,sort_keys=True)+'\n')
summary=dict(lean_processes=100,kani_runs=0,accepted=sum(r['exit_status']==0 for r in receipts),rejected=len(failures),final_validated_modules=len(valid),total_lean_wall_seconds=sum(r['wall_seconds'] for r in receipts),maximum_reported_rss_kib=max(int(r['peak_rss_kib']) for r in receipts),swaps=0,final_target=receipts[-1]['sources'],final_receipt=receipts[-1],scope='cached focused host compilation; no clean release/package replay')
(P/'JGa_SUMMARY.json').write_text(json.dumps(summary,indent=2)+'\n')
ledger=json.loads((R/'evidence/joint-fixture13-20261026/JFy_LEDGER_DELTA.json').read_text())
for row in ledger:
 root=row['target'].split('.')[1]
 before=P/f'JGa_BEFORE_{root}.lean.txt';after=P/f'JGa_AFTER_{root}.lean.txt'
 after.write_bytes((R/'lean'/f'{root}.lean').read_bytes())
 assert before.read_bytes()==after.read_bytes()
 row['before_source_sha256']=sha(before);row['after_source_sha256']=sha(after)
(P/'JGa_LEDGER_DELTA.json').write_text(json.dumps(ledger,indent=2)+'\n')
for stage,attempt in [('BEFORE','JGa14_001'),('AFTER','JGa14_100')]:
 log=(P/attempt/'stdout.log').read_text()
 for name in ['Rc7_Top.deployed','Rc10_Top.deployed','JGa_Fixture.inhabited','JGa_CopyFixture.inhabited']:
  start=log.find('theorem AspisR1.'+name+' :')
  if start<0:continue
  end=log.find("'AspisR1."+name+"' depends on axioms:",start)
  assert end>start
  (P/f'JGa_{stage}_{name.split(".")[0]}_KERNEL.txt').write_text(log[start:end])
for f in P.rglob('*'):
 if f.is_file():assert f.suffix not in ['.olean','.ir','.pyc','.elf','.o','.a','.so','.gz','.tar'],f
source_checks=dict(validated_current_sources=len(valid),unchecked=[],forbidden_source_constructs=[],binary_artifacts=[],before_after_top_sources_identical=True,shipped_source_changes=False)
(P/'JGa_STATIC_CHECKS.json').write_text(json.dumps(source_checks,indent=2)+'\n')
print(json.dumps({k:v for k,v in summary.items() if k!='final_receipt'},indent=2))
