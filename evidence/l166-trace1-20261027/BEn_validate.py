from pathlib import Path
import json,re,hashlib,subprocess
P=Path(__file__).resolve().parent;R=P.parents[1]
receipts=[]
for n in range(1,101):
 a=f'BEn_{n:03}';r=json.loads((P/a/'receipt.json').read_text())
 assert r['attempt']==a
 assert r['limits']=={'memory.high':'6442450944','memory.max':'8589934592','memory.swap.max':'0','pids.max':'64'}
 assert '-M7000' in r['command'] and r['swaps']=='0'
 for name,sha in r['source_hashes'].items():
  assert hashlib.sha256((P/a/'sources'/name).read_bytes()).hexdigest()==sha
 assert r['exit_status']==(1 if n in [11,13] else 0)
 if r['exit_status']==0:
  assert 'error:' not in (P/a/'stdout.log').read_text()
  for line in r['print_axioms']:
   names=re.search(r'\[([^]]*)\]',line)
   if names: assert set(x.strip() for x in names[1].split(',') if x.strip()) <= {'propext','Classical.choice','Quot.sound'},line
 receipts.append(r)
assert (P/'BEn_BEFORE_statement.lean.txt').read_bytes()==(P/'BEn_AFTER_statement.lean.txt').read_bytes()
assert (P/'BEn_BEFORE_kernel.txt').read_bytes()==(P/'BEn_AFTER_kernel.txt').read_bytes()
for source in (R/'lean').glob('BEn_*.lean'):
 text=source.read_text()
 assert not re.search(r'\b(sorry|axiom|admit|native_decide)\b|set_option (maxRecDepth|maxHeartbeats)',text)
 # Every added named theorem has its own print audit.
 for theorem in re.findall(r'^theorem (\w+)',text,re.M):assert '#print axioms '+theorem in text,(source,theorem)
changed=subprocess.check_output(['git','diff','--name-only','ff20ac7673cd03ffd1b989d3a19ea6d743145d99','HEAD'],text=True).splitlines()
assert all(x.startswith('lean/BEn_') or x.startswith('evidence/l166-trace1-20261027/BEn_') for x in changed)
assert len(json.loads((P/'BEn_AUDIT_PLAN.json').read_text()))==85
out=dict(lean_attempts=100,passed=98,excluded_failures=[11,13],kani_runs=0,extraction_runs=0,package_replays=0,frozen_manifest_replays=0,scope_policy='one at a time; 6G/8G/Swap0/Tasks64; Lean -M7000',total_compiler_wall_seconds=sum(r['wall_seconds'] for r in receipts),peak_rss_kib=max(int(r['peak_rss_kib']) for r in receipts),swaps=0,final_receipt={k:receipts[-1][k] for k in ['attempt','source_revision','source_hashes','exit_status','wall_seconds','peak_rss_kib','swaps','print_axioms']},statement_equal=True,row_delta={'T':0,'P':-1,'G':0,'C':0},warning='85 attempts are distinct declaration/provenance inventories, not new proof progress or a coherent release replay.')
(P/'BEn_VALIDATION.json').write_text(json.dumps(out,indent=2)+'\n')
(P/'BEn_attempts.jsonl').write_text(''.join(json.dumps(r)+'\n' for r in receipts))
print(json.dumps(out,indent=2))
