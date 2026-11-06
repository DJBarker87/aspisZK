"""Local evidence audit; never launches a proof, native gate or host process."""
from pathlib import Path
import json,hashlib,lzma,collections,subprocess,re
E=Path(__file__).resolve().parent
sha=lambda p:hashlib.sha256(p.read_bytes()).hexdigest()
rows=[json.loads(p.read_text()) for p in E.glob('NKK_[LK][0-9][0-9][0-9]/receipt.json')]
counts=collections.Counter(r['kind'] for r in rows)
assert counts['lean']==100 and counts['kani']==50 and counts['extract']==0,counts
assert len({r['attempt'] for r in rows})==len(rows)
for r in rows:
 a=r['attempt'];ad=json.loads((E/(a+'-admission.json')).read_text())
 assert ad['exit']==0 and ad['reservation']['allowed'] is True,a
 assert json.loads((E/(a+'-disk.json')).read_text())['free_bytes']>=40_000_000_000,a
 assert r['limits']=={'memory.high':'6442450944','memory.max':'8589934592','memory.swap.max':'0','pids.max':'64'},(a,r['limits'])
 assert r['env']['CARGO_TARGET_DIR'].endswith('/codex-cx-tx2-resume-20261108/NKK_target'),a
 assert r['swaps']=='0',a
fields=['attempt','kind','module','exit_status','wall_seconds','peak_rss_kib','swaps','source_revision','source_hashes','print_axioms','limits']
(E/'NKK_RESULTS.json').write_text(json.dumps([{k:r[k] for k in fields} for r in sorted(rows,key=lambda x:x['attempt'])],indent=2)+'\n')
selected=json.loads((E/'NKK_SELECTED_SOURCES.json').read_text())
for m,s in selected.items():
 assert sha(E/(m+'.lean'))==s['sha256'],m
 r=json.loads((E/s['receipt']).read_text());assert r['exit_status']==0,m
 assert s['sha256'] in r['source_hashes'].values(),m
 assert all('sorryAx' not in a for a in r['print_axioms']),m
roots=json.loads((E/'NKK_AUDIT_ROOTS.json').read_text())['roots'];walks=[]
for entry in json.loads((E/'NKK_FINAL_WALK_MANIFEST.json').read_text()):
 p=E/entry['path'];assert sha(p)==entry['sha256'],p
 d=json.loads(p.read_text());assert d['exit_status']==0,p;walks+=d['results']
assert {r['root'] for r in walks}==set(roots) and len(walks)==len(roots)==110
standard={'propext','Classical.choice','Quot.sound'}
assert all(r['equal'] and set(r['walked_axioms'])<=standard for r in walks)
assert json.loads((E/'NKK_audit/scan/scan.json').read_text())['exit_status']==0
verify=json.loads((E/'NKK_EXPORT_VERIFY.json').read_text());assert verify['status']=='PASS' and verify['raw_roots']==110
assert json.loads((E/'NKK_CLOSED.json').read_text())['rows']==[]
delta=json.loads((E/'NKK_LEDGER_DELTA.json').read_text());assert delta['before']==delta['after'] and not delta['promotions']
for name,record in json.loads((E/'NKK_INPUT_INDEX.json').read_text()).items():
 raw=lzma.decompress((E/record['capsule']).read_bytes())
 assert len(raw)==record['bytes'] and hashlib.sha256(raw).hexdigest()==record['sha256'],name
assert not [str(p) for p in E.rglob('*') if p.is_file() and p.stat().st_size>20_000_000]
assert not list(E.rglob('__pycache__'))
base=subprocess.check_output(['git','rev-parse','cf768e6e3df^'],text=True).strip()
changed=subprocess.check_output(['git','diff','--name-only',base],text=True).splitlines()
assert all(n.startswith('evidence/tx2-resume-20261108/') for n in changed),changed
(E/'NKK_LOCAL_VERIFICATION.json').write_text(json.dumps(dict(status='PASS',receipts=len(rows),counts=dict(counts),selected_modules=len(selected),raw_roots=len(walks),standard_axioms=sorted(standard),changed_paths=len(changed),shipped_files_changed=False,input_capsules_verified=True,files_over20MB=0,keys_touched=False),indent=2)+'\n')
gates={}
for name,a in [('combined','NKK_L110'),('raw_ax2_last_group','NKK_L118'),('nfx','NKK_L114'),('source_pins','NKK_L115'),('export','NKK_L116'),('export_verify','NKK_L117')]:
 r=json.loads((E/a/'receipt.json').read_text());assert r['exit_status']==0,a
 gates[name]={k:r[k] for k in fields if k not in ['source_hashes','print_axioms']};gates[name]['receipt']=a+'/receipt.json'
report=dict(target='TX2:124',target_established=False,status='OPEN',composed_rows_closed=0,ledger_delta=0,baseline=delta['before'],budget=dict(kani=dict(used=50,limit=50),lean=dict(used=100,limit=100),extraction=dict(used=0,limit=0),support_jobs=sum(v for k,v in counts.items() if k not in ['lean','kani','extract'])),native_components=len(json.loads((E/'NKK_NATIVE_CERTIFICATES.json').read_text())['rows']),selected_modules=len(selected),raw_roots=len(walks),standard_axioms=sorted(standard),full_combined_audits=2,final_raw_walk_manifest='NKK_FINAL_WALK_MANIFEST.json',final_full_walk_timeout='NKK_L113/receipt.json',final_raw_walk_first10_parent_exit=124,first_audit='NKK_first_audit/',final_gates=gates,trust='Owner option-A native contract semantic transport is P6/D188 reclassification; existing runtime digest value trust retained; no new trust row',pending_trust_unused=['RuntimeCpiReadonlyEntry7'],full_manifest_replayed=False,shipped_files_changed=False,elf_rebuild_triggered=False,keys_touched=False,pushed=False,remaining='NKK_FAILING_STEP.md',member_disposition='NKK_REMAINING.md',retention=json.loads((E/'NKK_RETENTION.json').read_text()))
(E/'NKK_AUDIT.json').write_text(json.dumps(report,indent=2)+'\n')
print(json.dumps(dict(status='OPEN',target_established=False,kani=50,lean=100,roots=110,gate='PASS',ledger_delta=0)))
