"""Derive ledger from immutable receipts; keep old ledgers untouched."""
from pathlib import Path
import hashlib,json,re
R=Path(__file__).resolve().parents[3]
E=R/'docs/research/100bit-spend-path-20261013/evidence/prover-rw-20261023/native-drop-abi'
P=E/'packet'
sha=lambda p:hashlib.sha256(p.read_bytes()).hexdigest()
old=E.parent/'native-drop/ledger.json'
rows=[]
def metric(text,name):
 m=re.search(re.escape(name)+r':\s*(\d+)',text);return int(m[1]) if m else None
for a in range(13,16):
 p=P/f'backend/ProverRwNativeDropABI-build-{a:03d}/receipt.json';d=json.loads(p.read_text()); t=d['time_log']
 rows.append(dict(kind='backend',attempt=a,receipt=str(p.relative_to(E)),receipt_sha256=sha(p),command=d['command'],exit=d['exit_status'],wall_seconds=d['wall_seconds'],peak_rss_kib=metric(t,'Maximum resident set size (kbytes)'),swaps=metric(t,'Swaps'),source_revision=d['source_revision'],source_sha256=d['candidate_source_sha256'],dependency_manifest_sha256=d['dependency_manifest_sha256'],binary=d.get('versioned_binary'),print_axioms=d['print_axioms'],accepted_artifact=False))
for a in range(36,45):
 p=P/f'extraction{a:03d}/receipt.json';d=json.loads(p.read_text())
 rows.append(dict(kind='extraction',attempt=a,receipt=str(p.relative_to(E)),receipt_sha256=sha(p),case=d['kind'],**{k:d[k] for k in ['command','scope_command','exit_status','wall_seconds','peak_rss_kib','swaps','source_revision','source_sha256','dependency_fingerprint','drop_flags','print_axioms','accepted_artifact']},category='extraction'))
J=Path('/home/dombarker/project-offloads/aspis-joint-20261019')
envp=Path('/home/dombarker/project-offloads/r1-privacy-build-integration-20261019/env/J.json')
# This exact env is retained by hash in packet/source-assessment; runner inspected.
lean='/home/dombarker/.elan/toolchains/leanprover--lean4---v4.32.0/bin/lean'
for a in range(11570,11576):
 p=P/f'lean/{a}-receipt.json';d=json.loads(p.read_text()); t=d['time_log'];m=d['module']
 command=[lean,'-j1','-M7000','-DElab.async=false','-R',str(J/'sources'),'-o',str(J/'objects'/(m+'.olean')),str(J/'sources'/(m+'.lean'))]
 rows.append(dict(kind='lean',attempt=a,receipt=str(p.relative_to(E)),receipt_sha256=sha(p),command=command,command_assessment='Expanded from inspected run2.py and pinned env J; raw launcher/runner hash and scope receipts retained.',exit=d['exit_status'],wall=re.search(r'Elapsed \(wall clock\) time \(h:mm:ss or m:ss\):\s*(\S+)',t)[1],peak_rss_kib=metric(t,'Maximum resident set size (kbytes)'),swaps=metric(t,'Swaps'),source_revision=d['source_revision'],source_sha256=d['source_sha256'],dependencies=d['dependencies'],dependency_fingerprint=d['deps_fingerprint'],print_axioms=d['print_axioms'],errors=d['errors']))
ledger=dict(schema='ProverRwNativeDropABI-ledger-v2',parent_ledger_sha256=sha(old),backend_used=15,backend_ceiling=16,backend_remaining=1,extraction_used=44,extraction_ceiling=44,extraction_remaining=0,lean_used=236,lean_ceiling=260,lean_remaining=24,kani_used=44,kani_ceiling=60,kani_remaining=16,rows=rows,claim='Printer precedence errors removed on actual unaccepted Guard emission; ordinary noDrop13 full closure checked; structural permutation facts only. No complete typed source/loan relation or destructor theorem.',premises_before_after='All existing native/refinement/E1 statements identical. No assumptions added or discharged. No counter1 premise or cleanup/output equality assumption.',stop='Actual nested borrow read/copy blockers, unresolved builtin pair/triple ABI, extraction allocation exhausted. No Zeroizing/provider/OS/E1/adoption work.',source_assessment='Dirty source labels are not fresh source identity gates: exact per-file/build/binary hashes are authoritative. See packet/source-assessment.json for post-run assessments and preserved-data limitation.')
ledger['supplied_current_elf_pins_not_revalidated']={'default':'f8c0ec72621fd5029a97d796c4a3623d0dc44a8e7074122372f9872915d143d4','devnet':'63ad3e9cc096dcbb55b3ca7ac7c8e89e6a845796ab5e4f5b7d15db96f3784299','Pool':'121f3e29741f510e6dc42d0345fc3c36217600f0be337094855c4a9da2581548'}
(E/'ledger.json').write_text(json.dumps(ledger,indent=2)+'\n')
# Compare the actual ordinary increment declaration independently of namespace.
raw=P/'extraction036/raw-output/Funs.lean.txt'; baseline=E.parent/'native-drop/packet/extraction032/raw-output/Funs.lean.txt'
extract=lambda p:re.search(r'def increment[\s\S]*?(?=\n\n|\nend )',p.read_text())[0]
a,b=extract(raw),extract(baseline);assert a==b
(E/'nodrop-comparison.json').write_text(json.dumps(dict(new_raw=str(raw.relative_to(R)),new_raw_sha256=sha(raw),baseline_raw=str(baseline.relative_to(R)),baseline_raw_sha256=sha(baseline),declaration_sha256=hashlib.sha256(a.encode()).hexdigest(),byte_identical_declaration=True,scope='candidate013 extraction036 only; no destructor semantics'),indent=2)+'\n')
# Check every exported receipt/blob against its retained integrity manifest.
for r in json.loads((P/'integrity.json').read_text()):
 p=P/r['path'];assert p.stat().st_size==r['bytes'] and sha(p)==r['sha256'],str(p)
print(json.dumps(dict(rows=len(rows),budgets={k:ledger[k] for k in ['backend_used','extraction_used','lean_used','kani_used']},all_measured_swaps_zero=all(r.get('swaps')==0 for r in rows))))
