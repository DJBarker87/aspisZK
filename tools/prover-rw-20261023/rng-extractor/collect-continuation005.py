"""Collect immutable receipts; launch no builds, extractions, proofs or tests."""
from pathlib import Path
import json,hashlib,re
R=Path(__file__).resolve().parents[3];E=R/'docs/research/100bit-spend-path-20261013/evidence/prover-rw-20261023/rng-extractor';C=E/'continuation005'
sha=lambda p:hashlib.sha256(p.read_bytes()).hexdigest()
prior=json.loads((E/'ledger.json').read_text());assert prior['backend_build_used']==4 and prior['extraction_used']==3 and prior['lean_cumulative_used']==213
rows=[]
def metric(t,n):return int(re.search(re.escape(n)+r':\s*(\d+)',t)[1])
for a in range(5,8):
 p=C/f'prover-rw-rng-extractor-build-{a:03d}/receipt.json';x=json.loads(p.read_text());t=x['time_log']
 assert x['limits']=={'memory.high':str(6*2**30),'memory.max':str(8*2**30),'memory.swap.max':'0','pids.max':'64'}
 assert metric(t,'Swaps')==0
 rows.append(dict(kind='backend-build',attempt=a,receipt=str(p.relative_to(C)),receipt_sha256=sha(p),target=x['command'],source_revision=x['source_revision'],source_hashes_field='candidate_source_sha256',exit=x['exit_status'],wall_seconds=x['wall_seconds'],peak_rss_kib=metric(t,'Maximum resident set size (kbytes)'),swaps=0,print_axioms=x['print_axioms']))
for a in range(4,13):
 p=C/f'extraction-{a:03d}/receipt.json';x=json.loads(p.read_text());assert x['swaps']==0 and x['cgroup_swap_peak_bytes']==0
 rows.append(dict(kind='extraction',attempt=a,receipt=str(p.relative_to(C)),receipt_sha256=sha(p),target=x['target'],source_revision=x['source_revision'],source_assessment='Historical host revision label; exact inputs/source hashes retained; see selected-source-assessment.json and candidate manifests. Not a new ELF identity gate.',dependency_fingerprint=x['deps_fingerprint'],exit=x['exit_status'],wall_seconds=x['wall_seconds'],peak_rss_kib=x['peak_rss_kib'],swaps=x['swaps'],print_axioms=x['print_axioms']))
env=json.loads((C/'lean-command-environment.json').read_text());H='/home/dombarker/project-offloads/aspis-joint-20261019'
for a in range(11553,11559):
 p=C/f'rng-extractor-lean005/{a}-receipt.json';x=json.loads(p.read_text());t=x['time_log'];assert metric(t,'Swaps')==0
 axioms=x['print_axioms']
 if x['exit_status']==0:assert all('sorryAx' not in s for s in axioms)
 module=x['module']
 cmd=[env['LEAN'],'-j1','-M7000','-DElab.async=false','-R',H+'/sources','-o',H+'/objects/'+module+'.olean',H+'/sources/'+module+'.lean']
 rows.append(dict(kind='lean',attempt=a,receipt=str(p.relative_to(C)),receipt_sha256=sha(p),target=cmd,LEAN_PATH=H+'/objects:'+env['LEAN_PATH'],source_revision=x['source_revision'],source_sha256=x['source_sha256'],dependency_fingerprint=x['deps_fingerprint'],exit=x['exit_status'],wall=t.split('Elapsed (wall clock) time (h:mm:ss or m:ss): ')[1].splitlines()[0],peak_rss_kib=metric(t,'Maximum resident set size (kbytes)'),swaps=0,print_axioms=axioms))
ledger=dict(schema='ProverRwRngExtractor-continuation005-ledger-v1',prior_ledger_sha256=sha(E/'ledger.json'),historical_backend_ceiling=4,extension_build_ids=[5,6,7,8],backend_build_used=7,backend_build_ceiling=8,backend_build_remaining=1,extraction_used=12,extraction_ceiling=12,extraction_remaining=0,lean_new=6,lean_cumulative_used=219,lean_ceiling=220,lean_remaining=1,kani_cumulative_used=44,kani_ceiling=60,kani_remaining=16,rows=rows,stop='Extraction ceiling exhausted; whole callback rejected by Lean; candidate007 rejects Drop/escaping-reference crates. No further launch or full manifest authorized.',validation_scope='candidate005 local operations checked; candidate007 negative preflight checked only; no whole-feature acceptance or provider-state transport')
(C/'ledger.json').write_text(json.dumps(ledger,indent=2)+'\n')
# Immutable source/receipt integrity, including old evidence; large derived JSON is hash+size only.
files={str(p.relative_to(R)):dict(sha256=sha(p),bytes=p.stat().st_size) for base in [C,R/'tools/prover-rw-20261023/rng-extractor'] for p in base.rglob('*') if p.is_file() and p.name!='integrity.json' and '__pycache__' not in p.parts}
for p in C.rglob('*.json'):assert p.stat().st_size<=5_000_000,p
(C/'integrity.json').write_text(json.dumps(files,indent=2)+'\n')
print(json.dumps({k:v for k,v in ledger.items() if k!='rows'}))
