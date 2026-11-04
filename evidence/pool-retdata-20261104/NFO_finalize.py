from pathlib import Path
import json,hashlib,subprocess,lzma,tomllib
E=Path(__file__).resolve().parent
sha=lambda b:hashlib.sha256(b).hexdigest()
receipts=[json.loads(p.read_text())|{'receipt_path':str(p.relative_to(E))} for p in sorted(E.glob('NFO_*/receipt.json'))]
k=[r for r in receipts if r['attempt'].startswith('NFO_K')];l=[r for r in receipts if r['attempt'].startswith('NFO_L')];e=[r for r in receipts if r['attempt'].startswith('NFO_E')]
assert (len(k),len(l),len(e))==(60,40,1)
for r in receipts:
 assert r['limits']=={'memory.high':'6442450944','memory.max':'8589934592','memory.swap.max':'0','pids.max':'64'}
 assert str(r['swaps'])=='0'
for i in range(1,61):
 prefix=f'NFO_K{i:03}'
 assert json.loads((E/(prefix+'-graph-check.json')).read_text())['graph_matches_frozen']
 assert json.loads((E/(prefix+'-lock-check.json')).read_text())['unchanged']
 assert json.loads((E/(prefix+'-rule16-check.json')).read_text())['no_writable_static']
metrics={'budget':{'kani':{'used':len(k),'limit':60},'lean_including_links_audits_scan':{'used':len(l),'limit':40},'extraction':{'used':len(e),'limit':3}},'total_used':len(receipts),'total_limit':103,'per_attempt_fields':'Every complete receipt records exact command/target, exit, wall_seconds, peak_rss_kib, swaps, source_revision, source_hashes, dependency pins, cgroup limits and print_axioms; source snapshots are retained. These are focused jobs, not release results.','max_peak_rss_kib':max(int(r['peak_rss_kib']) for r in receipts),'swap_total':sum(int(r['swaps']) for r in receipts),'attempts':[{kk:vv for kk,vv in r.items() if kk!='deps_fingerprint'} | {'full_receipt_sha256':sha((E/r['receipt_path']).read_bytes()),'dependency_pins_ref':r['receipt_path']} for r in receipts]}
(E/'NFO_RECEIPTS.json').write_text(json.dumps(metrics,indent=1)+'\n')
# Separate reference dependency check: only the local wrapper is new; no registry crates.
frozen=tomllib.loads(subprocess.check_output(['git','show','4bb3b3f51e16b4525f1d10336e2b0bcbbd775387:Cargo.lock'],text=True))
ref=tomllib.loads((E/'NFO_E001_outputs/NFO_ref__Cargo.lock').read_text())
key=lambda p:(p['name'],p['version'],p.get('source'))
fk={key(p) for p in frozen['package']};added=[key(p) for p in ref['package'] if key(p) not in fk]
assert added==[('nfo_decode_reference','0.1.0',None)],added
(E/'NFO_REFERENCE_GRAPH.json').write_text(json.dumps(dict(classification='E001 reference-only pruned lock, not a frozen Kani lock; actual frozen crates copied in NFO_src',reference_packages=ref['package'],new_local_wrapper_only=added,registry_packages=[p for p in ref['package'] if 'source' in p],cfg_if_libc_reached=False),indent=1)+'\n')
# All selected successful proof sources must match the current owned source.
latest={}
for r in sorted(l,key=lambda r:int(r['attempt'][5:])):
 if r['kind']=='lean' and r['exit_status']==0:latest[r['module']]=r
selected={}
for module,r in latest.items():
 p=E/(module+'.lean')
 if not p.exists():continue
 snapshot=E/r['attempt']/'NFO_SOURCE.lean.txt'
 assert p.read_bytes()==snapshot.read_bytes(),module
 selected[module]=dict(source_sha256=sha(p.read_bytes()),receipt=r['receipt_path'])
(E/'NFO_CHECKED_SOURCES.json').write_text(json.dumps(selected,indent=1)+'\n')
print(json.dumps({k:v for k,v in metrics.items() if k!='attempts'}))
