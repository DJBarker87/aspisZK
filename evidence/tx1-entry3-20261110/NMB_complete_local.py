"""Final local index validation and complete budget/resource accounting."""
from pathlib import Path
import json,hashlib,lzma,subprocess,shutil
E=Path(__file__).resolve().parent
sha=lambda p:hashlib.sha256(p.read_bytes()).hexdigest()
rows=[json.loads(l)for l in(E/'NMB_ATTEMPTS.jsonl').read_text().splitlines()];assert len(rows)==180 and len({r['attempt']for r in rows})==180
assert sum(r['kind']=='kani'for r in rows)==40 and sum(r['kind']!='kani'for r in rows)==140
for r in rows:
 p=E/r['attempt']/'receipt.json';assert sha(p)==r['deps_fingerprint_ref']['sha256']
 a=json.loads((E/(r['attempt']+'-admission.json')).read_text());assert a['exit']==0 and a['reservation']['allowed']is True
 assert r['swaps']=='0'
 assert r['limits']=={'memory.high':'6442450944','memory.max':'8589934592','memory.swap.max':'0','pids.max':'64'}
disk={}
for l in(E/'NMB_DISK.jsonl').read_text().splitlines():
 d=json.loads(l);disk[d['attempt']]=d
assert all(disk[r['attempt']]['free_bytes']>=40_000_000_000 for r in rows)
index=json.loads((E/'NMB_INPUTS.json').read_text())
for h,v in index['objects'].items():
 p=E/v['path'];assert sha(p)==v['archive_sha256'];assert hashlib.sha256(lzma.decompress(p.read_bytes())).hexdigest()==h
closure=json.loads((E/'NMB_CLOSURE_SUMMARY.json').read_text())
assert sha(E/'NMB_CLOSURE_PINS.json.xz')==closure['archive_sha256']
assert hashlib.sha256(lzma.decompress((E/'NMB_CLOSURE_PINS.json.xz').read_bytes())).hexdigest()==closure['json_sha256']
frozen='5782e6a32026fdd95d252d0db7ea20b16716e6deb4f5a397e744886bb6ba22ef'
for i in range(1,41):
 a=f'NMB_K{i:03d}';g=json.loads((E/(a+'-graph-check.json')).read_text());assert g['graph_matches_frozen']and g['lock_sha256']==frozen
 p=E/(a+'-lock-check.json')
 if p.exists():assert json.loads(p.read_text())['unchanged']
 else:assert i==1 and json.loads((E/(a+'-post-timeout.json')).read_text())['unchanged']
plan=json.loads((E/'NMB_AUDIT_PLAN.json').read_text());source_passes={}
for m in plan['modules']:
 h=sha(E/(m+'.lean'));passes=[r for r in rows if r['kind']=='lean'and r['module']==m and r['exit_status']==0 and h in r['source_hashes'].values()];assert passes,m;source_passes[m]=passes[-1]['attempt']
audit=json.loads((E/'NMB_AUDIT.json').read_text());assert audit['required_roots']==11518 and audit['all_required_raw_roots_present']and audit['raw_standard_axioms_only']
assert json.loads((E/'NMB_FINAL_CHECK.json').read_text())['checks']
resources=dict(max_peak_rss_kib=max(int(r['peak_rss_kib'])for r in rows),max_cgroup_memory_peak_bytes=max(int(r['cgroup_memory_peak_bytes'])for r in rows),scope_wall_seconds=sum(r['wall_seconds']for r in rows),swaps=0,scope_concurrency=1,limits=rows[-1]['limits'])
audit.update(budget=dict(Kani=40,Lean_support=140,extraction=0),resources=resources,source_modules=len(source_passes),source_passes=source_passes,metrics_manifest='NMB_ATTEMPTS.jsonl',final_aggregation_receipt='NMB_L139/receipt.json',final_integrity_receipt='NMB_L140/receipt.json',export='NMB_EXPORT.json',retention='NMB_RETENTION.json',closure_pins='NMB_CLOSURE_PINS.json.xz',full_native_segment_fold_delivered=False,domain_findings='NMB_DOMAIN_FINDINGS.json')
(E/'NMB_AUDIT.json').write_text(json.dumps(audit,indent=1)+'\n')
(E/'NMB_BUDGET.json').write_text(json.dumps(dict(Kani=40,Lean_support=140,extraction=0,actual_capped_scopes=180,by_kind={k:sum(r['kind']==k for r in rows)for k in sorted({r['kind']for r in rows})},actual_lean_compiler_invocations=sum(r['kind']=='lean'for r in rows),budget_convention='Every non-Kani capped host scope conservatively charged to Lean/support',prelaunch_refusals_not_launched=True,unused_scope_ids=[],resources=resources),indent=1)+'\n')
for p in E.rglob('__pycache__'):shutil.rmtree(p)
assert not[p for p in E.rglob('*')if p.is_file()and p.stat().st_size>20_000_000]
assert all(r.decode()[3:].startswith(str(E.relative_to(E.parents[1]))+'/NMB_')for r in subprocess.check_output(['git','status','--porcelain','-z']).split(b'\0')if r)
print(json.dumps(dict(checks=True,scopes=180,modules=len(source_passes),roots=11518,row_promotions=0,target_established=False,resources=resources)))
