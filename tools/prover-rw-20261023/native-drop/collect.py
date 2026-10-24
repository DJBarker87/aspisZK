"""Read-only local receipt validation and bounded continuation ledger."""
from pathlib import Path
import hashlib,json,re,subprocess
R=Path(__file__).resolve().parents[3]
E=R/'docs/research/100bit-spend-path-20261013/evidence/prover-rw-20261023/native-drop'
P=E/'packet';sha=lambda p:hashlib.sha256(p.read_bytes()).hexdigest()
ledger=E/'ledger.json';history=E/'ledger-compliance.json'
if not history.exists():history.write_bytes(ledger.read_bytes())
rows=[]
def metric(t,label):
 m=re.search(re.escape(label)+r':\s*(\d+)',t);return int(m[1]) if m else None
for a in range(8,13):
 p=P/'backend'/f'prover-rw-native-drop-build-{a:03d}/receipt.json';x=json.loads(p.read_text());before=json.loads((p.parent/'reservation-before-create.json').read_text());assert before['allowed']
 if a!=8:
  barrier=json.loads((p.parent/'reservation-at-barrier.json').read_text());assert barrier['allowed'] and barrier['projected_reserved_bytes']<55*2**30
  assert x['limits']=={'memory.high':str(6*2**30),'memory.max':str(8*2**30),'memory.swap.max':'0','pids.max':'64'}
 t=x.get('time_log') or ''
 rows.append(dict(kind='backend',attempt=a,receipt=str(p.relative_to(E)),receipt_sha256=sha(p),command=x['command'],exit=x['exit_status'],wall_seconds=x.get('wall_seconds'),peak_rss_kib=metric(t,'Maximum resident set size (kbytes)'),swaps=metric(t,'Swaps'),print_axioms=x['print_axioms'],source_revision_recorded=x['source_revision'],source_manifest_field='candidate_source_sha256',dependency_manifest_sha256=x['dependency_manifest_sha256'],binary=x.get('versioned_binary'),metric_scope='No workload launched for008; metrics unavailable. Other rows measure capped compiler.'))
for a in range(25,36):
 p=P/f'extraction{a:03d}/receipt.json';x=json.loads(p.read_text());barrier=json.loads((p.parent/'admission-barrier.json').read_text());assert barrier['allowed'] and barrier['projected_reserved_bytes']<55*2**30
 assert x['swaps']==0
 rows.append(dict(kind='extraction',attempt=a,receipt=str(p.relative_to(E)),receipt_sha256=sha(p),command=x['command'],scope_command=x['scope_command'],exit=x['exit_status'],wall_seconds=x['wall_seconds'],peak_rss_kib=x['peak_rss_kib'],swaps=x['swaps'],print_axioms=x['print_axioms'],source_revision_recorded=x['source_revision'],source_hashes_field='source_sha256',dependency_fingerprint=x['dependency_fingerprint'],accepted_artifact=False))
env=json.loads((E.parent/'native-entropy/lean-command-environment.json').read_text());J='/home/dombarker/project-offloads/aspis-joint-20261019'
for a in range(11563,11570):
 d=E/'lean' if a<=11564 else P/'lean';p=d/f'{a}-receipt.json';x=json.loads(p.read_text());barrier=json.loads((d/f'{a}-admission-barrier.json').read_text());assert barrier['allowed'] and barrier['own_limits']=={'memory.high':str(5*2**30),'memory.max':str(7*2**30),'memory.swap.max':'0','pids.max':'64'}
 t=x['time_log'];assert metric(t,'Swaps')==0;assert sha(d/f'{a}.lean.txt')==x['source_sha256']
 cmd=[env['LEAN'],'-j1','-M7000','-DElab.async=false','-R',J+'/sources','-o',J+'/objects/'+x['module']+'.olean',J+'/sources/'+x['module']+'.lean']
 rows.append(dict(kind='lean',attempt=a,receipt=str(p.relative_to(E)),receipt_sha256=sha(p),command=cmd,LEAN_PATH=J+'/objects:'+env['LEAN_PATH'],exit=x['exit_status'],wall=t.split('Elapsed (wall clock) time (h:mm:ss or m:ss): ')[1].splitlines()[0],peak_rss_kib=metric(t,'Maximum resident set size (kbytes)'),swaps=0,source_revision_recorded=x['source_revision'],source_sha256=x['source_sha256'],dependencies=x['dependencies'],dependency_fingerprint=x['deps_fingerprint'],print_axioms=x['print_axioms'],full_axioms_audit=11564 if a<=11564 else 11569,errors=x['errors']))
prior=E.parent/'native-entropy/ledger.json'
out=dict(schema='ProverRwNativeDrop-ledger-v2',prior_ledger_sha256=sha(prior),compliance_ledger_sha256=sha(history),backend_used=12,backend_ceiling=12,backend_remaining=0,extraction_used=35,extraction_ceiling=36,extraction_remaining=1,lean_used=230,lean_ceiling=260,lean_remaining=30,kani_used=44,kani_ceiling=60,kani_remaining=16,rows=rows,source_assessment='Receipt revisions are historical dirty labels, not new git or ELF identity gates. Per-attempt exact source snapshots/manifests and dependency/binary hashes identify actual candidate inputs. No shipped host source changed.',claim='Generated-limit compliance and ordinary noDrop full closure checked. Candidate012 real glue translation remains unaccepted: entire Guard emission fails kernel/type checking. No source simulation theorem or assumption discharge.',stop='Backend allocation exhausted and concrete nested-loan ABI/output syntax blockers demonstrated; no Zeroizing/provider work.',premises_before_after='All existing native/refinement statements identical. No new assumptions, no discharged assumptions.',default_correction='Config default true; older baseline command labels false unsupported. See packet/default-assessment.json.',reused='Pinned V5 native counter result; retained baseline association, LLBC/source pins, prior scanner/Docker fixtures, prior local proofs at documented scopes only.',case31='Legacy mutated LLBC rejection, not an escaping reference fixture. Actual native escape/capture rejection035.')
ledger.write_text(json.dumps(out,indent=2)+'\n')
for p in E.rglob('*.json'):assert p.stat().st_size<=5_000_000,p
manifest={str(p.relative_to(R)):dict(sha256=sha(p),bytes=p.stat().st_size) for root in [E,R/'tools/prover-rw-20261023/native-drop'] for p in root.rglob('*') if p.is_file() and p.name!='integrity.json' and '__pycache__' not in p.parts}
(E/'integrity.json').write_text(json.dumps(manifest,indent=2)+'\n')
print(json.dumps({k:v for k,v in out.items() if k.endswith(('_used','_remaining'))}))
