"""Validate and summarize only this worker's retained evidence; no prover launch."""
from pathlib import Path
import json,hashlib,subprocess,re,lzma
E=Path(__file__).resolve().parent
read=lambda p:json.loads(p.read_text())
sha=lambda p:hashlib.sha256(p.read_bytes()).hexdigest()
receipts=[read(p)for p in sorted(E.glob('NIT_[KL][0-9][0-9][0-9]/receipt.json'))]
lean=[r for r in receipts if r['kind']!='kani'];kani=[r for r in receipts if r['kind']=='kani']
assert len(lean)==120 and len(kani)==4
assert len((E/'NIT_ATTEMPTS.jsonl').read_text().splitlines())==124
assert all(str(r['swaps'])=='0' for r in receipts)
for r in receipts:
 ad=read(E/(r['attempt']+'-admission.json'))
 assert ad['exit']==0 and ad['reservation']['allowed'] is True
 assert r['exit_status'] in [0,1],r['attempt']
 assert r['command'] and r['source_revision'] and r['deps_fingerprint']['selected_objects']
raw=[json.loads(l[11:])for l in(E/'NIT_L140/stdout.log').read_text().splitlines()if l.startswith('NEP_RESULT ')]
roots=read(E/'NIT_AUDIT_ROOTS.json')['groups'][0]
assert len(raw)==len(roots)==158 and {r['root']for r in raw}==set(roots)
assert all(r['equal']and set(r['walked_axioms'])<={'propext','Classical.choice','Quot.sound'}for r in raw)
scan=[json.loads(l)for l in(E/'NIT_LOADED_scan.jsonl').read_text().splitlines()]
assert len(scan)==13788 and all(not r['dangling']and not r['duplicate_owners']and r['imports_match']for r in scan)
pins=read(E/'NIT_AUDIT_PINS.json')
for attempt in ['NIT_L139','NIT_L140','NIT_L141']:
 for role,driver in [('proof','NIT_ProofDriver'),('scanner','NIT_Driver')]:
  assert read(E/(attempt+'/'+driver+'_BINARY_PIN.json'))==pins[role]
for p in E.glob('NEP_*_REACHABLE.txt.xz'):
 data=lzma.decompress(p.read_bytes())
 assert hashlib.sha256(data).hexdigest()==p.with_suffix('').with_suffix('.txt.sha256').read_text().split()[0]
for p in E.rglob('*'):
 if p.is_file():assert p.stat().st_size<=20_000_000,p
assert not list(E.rglob('__pycache__'))
for x in read(E/'NIT_AUDIT_PROVENANCE.json')['semantic_modules']:
 p=E/x['path'];assert sha(p)==x['sha256']
 assert not re.search(r'(?m)^\s*(axiom |sorry\b|admit\b)',p.read_text()),p
assert read(E/'NIT_CLOSED.json')['closed_rows']==[]
resources=[]
for r in receipts:
 resources.append({k:r[k]for k in ['attempt','kind','module','command','exit_status','wall_seconds','peak_rss_kib','swaps','source_revision']})
(E/'NIT_FINAL_RESOURCES.json').write_text(json.dumps(dict(lean_link_audit=120,kani=4,extraction=0,peak_rss_kib=max(int(r['peak_rss_kib'])for r in receipts),total_wall_seconds=sum(r['wall_seconds']for r in receipts),all_swaps_zero=True,scope='Every admitted scope MemoryHigh=6G MemoryMax=8G MemorySwapMax=0 TasksMax=64; Lean-M7000; optimized native gates/linker',results=resources),indent=2)+'\n')
audit=dict(status='PASS_SUPPORTING_OBJECTS_ROWS_OPEN',combined=dict(attempt='NIT_L138',exit=0,imports=['NGK_COMBINED_IMPORT','NIG_COMBINED_IMPORT','NIQ_COMBINED_IMPORT','NIT modules','AspisR1.RPx_Deployed.deployed']),raw_ax2=dict(attempt='NIT_L140',exit=0,roots=158,standard_only=True,axioms=['propext','Classical.choice','Quot.sound'],graphs='NEP_proof0_*_REACHABLE.txt.xz with uncompressed .sha256'),NFX_loaded_objects=dict(attempt='NIT_L141',exit=0,modules=len(scan),dangling=0,incompatible_owners=0,import_mismatches=0),fixtures=dict(attempt='NIT_L139',exit=0,count=8,exact_expected_graphs=True,binary_pins=pins),native=dict(credited_positive='NIT_K003',matched_failing_control='NIT_K004',excluded=['NIT_K001','NIT_K002'],frozen_graph_offline_unchanged_lock=True,KMX_exact=True,no_field_multiplication=True),budgets=dict(lean_link_audit_used=120,lean_link_audit_limit=120,kani_used=4,kani_limit=30,extraction_used=0,extraction_limit=0),headline_established=False,promoted_rows=[],trust='No additions/removals; option-A P6/D188 semantic transport reclassification retained; NIN-R2/RuntimeCpiReadonlyEntry7 unused',reproducibility='Per-attempt source snapshot, revision, argv, Aeneas/selected-object hashes and metrics retained; focused cached replay, not a full frozen-release rebuild')
(E/'NIT_AUDIT.json').write_text(json.dumps(audit,indent=2)+'\n')
failed=[r['attempt']for r in lean if r['exit_status']]
with (E/'NIT_FAILING_STEP.md').open('a')as f:
 f.write('\nFinal failed focused Lean diagnostics: '+', '.join(failed)+'. Each has its exact failed source/receipt. Final semantic sources compile and all158 roots pass raw ax2. No timeout/memory kill, cap increase, unchanged timed-out rerun, or extracted/shipped semantic change. The gaps remaining are uncompleted composition proofs, not counterexamples.\n')
 f.write('\nTranscript hygiene deviation: the stage5 git commit command emitted a long created-file list. Subsequent commits use quiet mode; no semantic/source or evidence change was concealed.\n')
print(json.dumps(dict(status=audit['status'],scopes=len(receipts),roots=len(raw),modules=len(scan),peak_rss_kib=max(int(r['peak_rss_kib'])for r in receipts))))
