"""Strict report construction: raw ax2 is authoritative; zero row promotion."""
from pathlib import Path
import hashlib,json,lzma,re,collections,subprocess
E=Path(__file__).resolve().parent;sha=lambda b:hashlib.sha256(b).hexdigest()
put=lambda n,x:(E/n).write_text(json.dumps(x,indent=1)+'\n')
receipts=[json.loads(l) for l in (E/'NLK_ATTEMPTS.jsonl').read_text().splitlines()]
byid={r['attempt']:r for r in receipts};assert len(byid)==len(receipts)
manifest=json.loads((E/'NLK_AUDIT_ROOTS.json').read_text());required=manifest['roots'];groups=manifest['groups'];standard={'Classical.choice','Quot.sound','propext'}
results=[];nonzero=[]
for i,g in enumerate(groups[:30]):
 a=f'NLK_L{56+i:03}';r=byid[a]
 text=lzma.open(E/a/'stdout.log.xz','rt').read()
 rows=[json.loads(l[len('NEP_RESULT '):]) for l in text.splitlines() if l.startswith('NEP_RESULT ')]
 assert {x['root'] for x in rows}==set(g),(a,len(rows),len(g))
 for x in rows:assert set(x['walked_axioms'])<=standard,(a,x['root'],x['walked_axioms'])
 results+=rows
 if r['exit_status']!=0:nonzero.append(dict(attempt=a,mode='proof'+str(i),exit_status=r['exit_status']))
a='NLK_L088';r=byid[a];text=lzma.open(E/a/'stdout.log.xz','rt').read()
rows=[json.loads(l[11:]) for l in text.splitlines() if l.startswith('NEP_RESULT ')]
assert {x['root'] for x in rows}==set(groups[30]+['AspisR1.RPx_Deployed.deployed','NHC_DecodeModel.decoder_error'])
assert r['exit_status']==1
nonzero.append(dict(attempt=a,mode='proof30',exit_status=1))
prior={x['root']:x for x in results}
for x in rows:
 assert set(x['walked_axioms'])<=standard,x['root']
 if x['root'] in prior:assert x==prior[x['root']],x['root']
 else:results.append(x)
assert len(results)==len(required)==len({x['root'] for x in results})
disagreements=[r for r in results if not r['equal']]
assert len(disagreements)==1 and disagreements[0]['root']=='NHC_DecodeModel.decoder_error',disagreements
assert disagreements[0]['collect_axioms']==[] and set(disagreements[0]['walked_axioms'])==standard
assert len(nonzero)==2 and all(r['exit_status']==1 for r in nonzero)
fixtures=[json.loads(l[11:]) for l in lzma.open(E/'NLK_L055/stdout.log.xz','rt').read().splitlines() if l.startswith('NEP_RESULT ')]
old=json.loads((E.parent/'ledger21-20261110/NLG_AUDIT.json').read_text())['fixtures']
assert {r['root']:r['walked_axioms'] for r in fixtures}=={r['root']:r['walked_axioms'] for r in old}
assert len(fixtures)==8 and all(r['equal'] for r in fixtures)
scan=[json.loads(l) for l in lzma.open(E/'NLK_LOADED_scan.jsonl.xz','rt').read().splitlines()]
assert all(r['imports_match'] and not r['dangling'] for r in scan)
assert byid['NLK_L091']['exit_status']==0
pins=json.loads(lzma.decompress((E/'NLK_CLOSURE_PINS.json.xz').read_bytes()));assert pins['scan_pass'] and not pins['mismatches']
for p in E.glob('NLK_binary_*.json'):
 x=json.loads(p.read_text());assert x['unchanged'] and x['before']==x['after']
# All new public theorem statements were printed and show only standard axioms.
text=lzma.open(E/'NLK_L087/stdout.log.xz','rt').read();printed={}
for line in text.splitlines():
 m=re.match(r"'([^']+)' depends on axioms: \[([^]]*)\]",line)
 if m:printed[m[1]]=set(x.strip() for x in m[2].split(',') if x.strip())
 m=re.match(r"'([^']+)' does not depend on any axioms",line)
 if m:printed[m[1]]=set()
for r in manifest['new_roots']:assert r in printed and printed[r]<=standard,r
mods=json.loads((E/'NLK_SEMANTIC_MODULES.json').read_text())
for m in mods:
 h=sha((E/(m+'.lean')).read_bytes())
 assert any(r['module']==m and r['exit_status']==0 and h in r['source_hashes'].values() for r in receipts),m
 assert not re.search(r'\b(sorry|admit|axiom|native_decide)\b', '\n'.join(l for l in (E/(m+'.lean')).read_text().splitlines() if not l.lstrip().startswith(('--','/--','*')))),m
native=json.loads((E/'NLK_NATIVE_VERDICTS.json').read_text());assert len(native)==60
assert all(r['graph_matches_frozen'] and r['lock_unchanged'] for r in native)
counts=collections.Counter(r['status'] for r in native)
# Per-attempt gate fields remain the authoritative resource records.
resources=dict(attempts=len(receipts),native_attempts=60,formal_scope_attempts=len(receipts)-60,budget=dict(kani=60,lean=110,extraction=0),wall_seconds=sum(float(r['wall_seconds']) for r in receipts),peak_rss_kib=max(int(r['peak_rss_kib']) for r in receipts if str(r['peak_rss_kib']).isdigit()),swaps=sorted(set(str(r['swaps']) for r in receipts)),caps=dict(MemoryHigh='6G',MemoryMax='8G',MemorySwapMax=0,TasksMax=64,LeanM=7000),attempts_file='NLK_ATTEMPTS.jsonl')
assert resources['formal_scope_attempts']<=110 and resources['swaps']==['0']
put('NLK_SCAN.json',dict(status='PASS',attempt='NLK_L091',exit_status=0,loaded_modules=len(scan),zero_dangling=True,imports_match=True,pins='NLK_CLOSURE_PINS.json.xz',aeneas_and_sidecars_pinned=True))
put('NLK_AUDIT.json',dict(status='PASS_LOCAL_SUPPORT_AUDIT_NO_ROW_PROMOTION_WITH_RETAINED_COLLECTOR_FINDING',security_target_established=False,row_composition_pass=False,proof_packet_composition_pass=True,combined='NLK_COMBINED_IMPORT',combined_attempt='NLK_L087',full_combined_audits=1,combined_import_attempts=2,import_repair_recheck='NLK_L088',unchanged_inherited_raw_reused=10720,import_finding='NLK_IMPORT_FINDING.json',failed_partial_batch_credited=False,headline='AspisR1.RPx_Deployed.deployed',required_roots=len(required),new_roots=len(manifest['new_roots']),all_required_raw_roots_present=True,raw_standard_axioms_only=True,axioms=sorted(standard),collect_axioms_disagreements=disagreements,raw_authoritative_ruling="(ax2), (ab')(3)",retained_nonzero_audit_exits=nonzero,proof_binary_sha256='d12d3e28ca5819cc41010e74078c49d7d64eec727472e4401949f6694c9e0675',fixtures=fixtures,scanner='NLK_SCAN.json',selected_objects=len(pins['selected_objects']),semantic_modules=mods,native_verdict_counts=dict(counts),resources=resources,cold_release_replay=False,elf_rebuild=False,source_stage_commit='256baac6480ddac8119b09ae6696cc64594e7239',hypotheses='NLK_HYPOTHESES.md',remaining='NLK_REMAINING.md',raw_references='NLK_RAW_REFERENCES.json',export='NLK_EXPORT.json'))
baseline=E.parent/'ledger21-20261110/NLG_LEDGER.json.xz';raw=lzma.decompress(baseline.read_bytes())
put('NLK_CLOSED.json',dict(status='NO_ROW_PROMOTION',rows=[],security_target_established=False,support_only=True,credit='Waits for a complete native packet and next authoritative ledger gate'))
put('NLK_LEDGER_DELTA.json',dict(baseline='evidence/ledger21-20261110/NLG_LEDGER.json.xz',baseline_archive_sha256=sha(baseline.read_bytes()),baseline_raw_sha256=sha(raw),baseline_counts=dict(CLOSED=564,QUALIFIED=0,OPEN=35,total=599),changes=[],result_counts=dict(CLOSED=564,QUALIFIED=0,OPEN=35,total=599),assigned_rows={k:'OPEN' for k in ['TX2:217','TX2:234','TX2:233','TX2:242']},authoritative=False,next_ledger_gate_required=True))
print(json.dumps(dict(raw_roots=len(required),new_theorems=len(manifest['new_roots']),scan_modules=len(scan),known_disagreements=len(disagreements),new_closed_rows=0,formal_attempts=resources['formal_scope_attempts'])))
