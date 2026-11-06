"""Assemble reporting from committed proof inputs and collected receipts; no prover launch."""
from pathlib import Path
import json,hashlib,re,collections
E=Path(__file__).resolve().parent
read=lambda n:json.loads((E/n).read_text())
write=lambda n,x:(E/n).write_text(json.dumps(x,indent=2)+'\n')
rows=[json.loads(l) for l in (E/'NLB_ATTEMPTS.jsonl').read_text().splitlines()]
assert len({r['attempt'] for r in rows})==len(rows)
counts=dict(collections.Counter(r['kind'] for r in rows))
roots=read('NLB_AUDIT_ROOTS.json')['roots'];results=[];groups=[]
for i in range(4):
 p=f'NLB_audit/batch{i}/proof{i}.json';r=read(p);assert r['exit_status']==0
 results+=r['results'];groups.append(dict(path=p,**{k:r[k] for k in ['exit_status','wall_seconds','peak_rss_kib','swaps']}))
assert {r['root'] for r in results}==set(roots) and len(results)==len(roots)
assert all(r['equal'] and set(r['walked_axioms'])<={'propext','Classical.choice','Quot.sound'} for r in results)
fixtures=[]
for mode,attempt in [('fixtures','NLB_L054'),('scanfixtures2','NLB_L066')]:
 r=read(f'NLB_audit/{mode}/fixtures.json');assert r['exit_status']==0 and len(r['results'])==8
 assert all(x['equal'] for x in r['results'])
 assert [x['walked_axioms'] for x in r['results']]==[['NEP_Planted.matchAx'],['NEP_Planted.privateAx'],['NEP_Planted.proofAx'],['NEP_Planted.auxAx'],[],[],[],[]]
 fixtures.append(dict(attempt=attempt,driver=mode,roots=8,all_equal=True))
scan=read('NLB_audit/scan/scan.json');assert scan['exit_status']==0
loaded=[json.loads(s) for s in (E/'NLB_LOADED_scan.jsonl').read_text().splitlines()]
bad=[r for r in loaded if r['dangling'] or r['duplicate_owners'] or not r['imports_match']];assert not bad
if (E/'NLB_SCAN_FINDINGS.json').exists() and read('NLB_SCAN_FINDINGS.json'):
 (E/'NLB_SCAN_FINDINGS_L060.json').write_text((E/'NLB_SCAN_FINDINGS.json').read_text())
write('NLB_SCAN_FINDINGS.json',bad)
conformance=read('NLB_WALKER_CONFORMANCE.json');conformance.update(fixtures=fixtures,scanner_initial_zero_root_command='NLB_L055 excluded',walker_unchanged=True);write('NLB_WALKER_CONFORMANCE.json',conformance)
verify=read('NLB_EXPORT_VERIFY.json');assert verify['status']=='PASS'
latest={}
for r in rows:
 if r['kind']=='lean' and r['exit_status']==0:latest[r['module']]=r
for m,h in read('NLB_SOURCE_PINS.json').items():
 assert m in latest,m
 # Match the exact uploaded source snapshot used by the passing compile.
 p=E/latest[m]['attempt']/'sources/NLB_generated'/(m+'.lean')
 assert hashlib.sha256(p.read_bytes()).hexdigest()==h,m
 for line in latest[m].get('print_axioms',[]):assert 'sorryAx' not in line,line
for p in E.glob('NLB_*.lean'):
 text=p.read_text();assert not re.search(r'^\s*(axiom|sorry|admit)\b|\bnative_decide\b|set_option\s+(maxRecDepth|maxHeartbeats)',text,re.M),p
assert all(v==0 for v in read('NLB_TARGET.json')['source_tree_checks'].values())
rawaxioms=sorted({a for r in results for a in r['walked_axioms']})
write('NLB_AUDIT.json',dict(status='PASS',scope='Coherent combined import, raw ax2 and NFX scan; NOT a native row certificate',target='TX2:065',target_established=False,exact_bd3_packet_parameterization_complete=False,composed_new_closed_rows=0,combined_import_attempt='NLB_L049',headline='AspisR1.RPx_Deployed.deployed',focused_modules=len(read('NLB_MODULES.json')),raw_roots=len(results),all_raw_equal=True,raw_axioms=rawaxioms,raw_groups=groups,fixtures=fixtures,scanner_attempt='NLB_L067',scanner_exit=0,loaded_modules=len(loaded),dangling=0,incompatible_owners=0,import_mismatches=0,full_combined_scans=2,combined_import_compiles=1,full_frozen_manifest_replays=0,corrections='NLB_AUDIT_CORRECTION.json',source_revision_and_metrics='NLB_ATTEMPTS.jsonl and full per-attempt receipts',export_verification=verify))
write('NLB_CLOSED.json',dict(status='SUPPORT_ONLY',target='TX2:065',target_established=False,closed=[],candidate_closed=[],open_rows=['TX2:065','TX2:124','TX2:053'],semantic_fold='NLB_Parent.native_fold',native_parent_certificate=False,exact_bd3_packet_parameterization_complete=False,reason='C01 is an undischarged observed-run packet; C04 ReplyRel is only the Result projection, lacking complete native internal digest/frame/error-prefix packet. No root emitted.',credit_gate='next authoritative ledger gate'))
baseline=Path('evidence/ledger20-20261109/NKW_LEDGER.json.xz')
write('NLB_LEDGER_DELTA.json',dict(baseline=str(baseline),baseline_sha256=hashlib.sha256(baseline.read_bytes()).hexdigest(),counts_before=dict(closed=560,qualified=0,open=39,total=599),counts_after=dict(closed=560,qualified=0,open=39,total=599),delta=dict(closed=0,qualified=0,open=0),promotions=[],target='TX2:065',target_status='OPEN',no_authoritative_ledger_modified=True))
write('NLB_RECEIPT_INDEX.json',dict(attempts=[dict(attempt=r['attempt'],kind=r['kind'],target=r['module'],receipt=r['full_receipt'],exit_status=r['exit_status']) for r in rows],processes=len(rows),counts=counts,budget=dict(kani=15,formal_support=150,extraction=0),used=dict(kani=0,formal_support=len(rows),extraction=0),max_peak_rss_kib=max(int(r['peak_rss_kib']) for r in rows),swaps=sorted({str(r['swaps']) for r in rows}),timeouts=0,memory_kills=0,all_scope_caps='MemoryHigh6G MemoryMax8G MemorySwapMax0 TasksMax64; Lean -M7000',cargo_target_dir='/home/dombarker/project-offloads/codex-cx-tx2-native11-20261109/NLB_target',failed_diagnostics=[r['attempt'] for r in rows if r['exit_status']],remaining='NLB_REMAINING.md'))
write('NLB_AXIOMS.json',dict(roots=results,standard_only=True,raw_equal_collectAxioms=True,failed_compile_sorryAx_excluded=True))
print(json.dumps(dict(attempts=len(rows),counts=counts,raw_roots=len(results),scan_modules=len(loaded),export_objects=verify['export_objects'],status='PASS',new_closed_rows=0)))
