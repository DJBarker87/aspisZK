from pathlib import Path
import json,hashlib,re,sys,subprocess,base64,lzma
p=Path(__file__).resolve().parent
sha=lambda q:hashlib.sha256(q.read_bytes()).hexdigest()
rows=[json.loads(l)for l in(p/'NLH_ATTEMPTS.jsonl').read_text().splitlines()]
assert len({r['attempt']for r in rows})==len(rows)
assert sum(r['kind']=='kani'for r in rows)<=50
assert sum(r['kind']!='kani'for r in rows)<=140
expected={'memory.high':'6442450944','memory.max':'8589934592','memory.swap.max':'0','pids.max':'64'}
graph_raw=lzma.decompress((p/'NLH_RESOLVED_GRAPH.json.xz').read_bytes());graph_digest=hashlib.sha256(graph_raw).hexdigest();assert graph_digest==(p/'NLH_RESOLVED_GRAPH.json.sha256').read_text().strip()
for r in rows:
 assert r['limits']==expected,r['attempt']
 admission=json.loads((p/(r['attempt']+'-admission.json')).read_text())
 assert admission['exit']==0 and admission['reservation']['allowed']is True,r['attempt']
 assert r['swaps']=='0',r['attempt']
 native_dir=r['env'].get('CARGO_TARGET_DIR')
 if r['kind']=='kani':
  assert native_dir=='/home/dombarker/project-offloads/codex-cx-terminal6-20261110/NLH_target'
  assert r['env']['CARGO_NET_OFFLINE']=='true'
  graph=json.loads((p/(r['attempt']+'-graph-check.json')).read_text());lock=json.loads((p/(r['attempt']+'-lock-check.json')).read_text());src=json.loads((p/(r['attempt']+'-source-check.json')).read_text())
  assert graph['graph_matches_frozen']and not graph['new_package_tuples']and not graph['edge_errors']
  ref=json.loads((p/(r['attempt']+'-graph.ref.json')).read_text());assert ref['raw_sha256']==graph['graph_sha256']==graph_digest and ref['raw_bytes']==len(graph_raw) and ref['archive']=='NLH_RESOLVED_GRAPH.json.xz'
  assert lock['unchanged']and lock['before']==lock['after']=='5782e6a32026fdd95d252d0db7ea20b16716e6deb4f5a397e744886bb6ba22ef'
  assert not src['errors']
assert hashlib.sha256((p/'NLH_KMX.patch').read_bytes()).hexdigest()=='bcdf749b78eb6143789500d98d64ec3d407b8a17a6d1290c70c822473e8e9a67'
for i in range(2,48):
 a=f'NLH_K{i:03}';r=next(r for r in rows if r['attempt']==a);s=(p/a/'stdout.log').read_text()
 assert r['exit_status']==(0 if i%2==0 else 1),a
 assert ('VERIFICATION:- SUCCESSFUL'in s if i%2==0 else 'VERIFICATION:- FAILED'in s),a
first=None;library=[]
for r in rows:
 rc=json.loads((p/r['attempt']/'receipt.json').read_text());pins=rc['deps_fingerprint']['selected_objects'];a={k:v for k,v in pins.items()if'/Aeneas'in k}
 if not a:continue
 if first is None:first=a
 assert a==first,r['attempt']
 library.append(dict(attempt=r['attempt'],objects=len(a),same_as_first=True))
(p/'NLH_LIBRARY_PARITY.json').write_text(json.dumps(dict(all_identical=True,objects=len(first or{}),rows=library),indent=1)+'\n')
closed=json.loads((p/'NLH_CLOSED.json').read_text())
for r in closed.get('functions',closed.get('rows',[])):
 f=p/(r['module']+'.lean');q=json.loads((p/r['receipt']).read_text());assert q['exit_status']==0 and sha(f)==q['source_hashes'][f.name]==r['source_sha256']
 assert not any('sorryAx'in s for s in q['print_axioms'])
passed=json.loads((p/'NLH_GATE_SOURCES.json').read_text())['passed']
for m in passed:
 s=(p/(m+'.lean')).read_text()
 assert not re.search(r'^\s*(?:axiom\s|unsafe\s|opaque\s)',s,re.M),m
 assert not re.search(r'\b(?:sorry|admit|native_decide)\b',s),m
large=[str(q)for q in p.rglob('*')if q.is_file()and q.stat().st_size>20000000];assert not large
if '--final'in sys.argv:
 gate=json.loads((p/'NLH_GATE_ATTEMPTS.json').read_text());audit=[]
 for mode,a in gate.items():
  r=next(r for r in rows if r['attempt']==a)
  if mode.startswith('proof')or mode in ['scan','fixtures']:
   x=json.loads((p/'NLH_audit'/mode/'receipt.json').read_text());audit.append(x)
  else:assert r['exit_status']==0
 fixtures=next(r for r in audit if r['target']=='fixtures');scan=next(r for r in audit if r['target']=='scan')
 assert fixtures['fixture_pass']and fixtures['exit_status']==0
 assert scan['exit_status']==0 and not(scan['dangling']or scan['duplicate_owners']or scan['import_mismatch'])
 scanbase=p/'NLH_audit'/'scan';scanraw=lzma.decompress(base64.b64decode((scanbase/'scan.jsonl.xz.b64.txt').read_text(),validate=True));assert hashlib.sha256(scanraw).hexdigest()==(scanbase/'scan.jsonl.sha256').read_text().strip();assert len(scanraw.splitlines())==scan['modules']
 proofs=[r for r in audit if r['target'].startswith('proof')];assert all(r['standard_only']for r in proofs)
 results=[x for r in proofs for x in r['results']];roots=json.loads((p/'NLH_AUDIT_ROOTS.json').read_text())['roots'];assert sorted(x['root']for x in results)==sorted(roots)
 differences=[x for r in proofs for x in r['collect_axioms_disagreements']];assert {x['root']for x in differences}=={'AspisR1.NKR_ScheduleExt.transition','NHC_DecodeModel.decoder_error'}
 assert all(r['exit_status']==(1 if r['collect_axioms_disagreements']else 0)for r in proofs)
 private='_private.NKR_SumCopyFull.0.AspisR1.NKR_SumCopyRoot.rows_ext';assert private in roots
 assert not re.search(r'^#check', (p/'NLH_COMBINED_IMPORT.lean').read_text(),re.M)
 for r in proofs:
  for x in r['raw_artifacts']:
   base=p/'NLH_audit'/r['target'];q=base/(x['name']+'.xz.b64.txt');assert q.is_file()and(base/(x['name']+'.sha256')).read_text().strip()==x['sha256']
   compressed=base64.b64decode(q.read_text(),validate=True);raw=lzma.decompress(compressed)
   assert len(compressed)==x['compressed_bytes']and len(raw)==x['bytes']and hashlib.sha256(raw).hexdigest()==x['sha256']
 report=dict(status='PASS',source_stage_revision='17196627cdb',headline='AspisR1.RPx_Deployed.deployed',combined_import=gate['combined'],combined_import_exit=0,combined_audits=1,own_modules=len(passed),new_theorem_roots=len(json.loads((p/'NLH_AUDIT_ROOTS.json').read_text())['new_roots']),raw_roots=len(results),raw_standard_only=True,private_inventory_retained=private,collector_disagreements=differences,original_raw_exits_retained=True,fixtures=dict(attempt=gate['fixtures'],exit=0,count=8),nfx_scan=dict(attempt=gate['scan'],exit=0,modules=scan['modules'],dangling=0,duplicate_owners=0,import_mismatch=0),kani_scopes=sum(r['kind']=='kani'for r in rows),kani_positive_control_pairs=23,lean_and_audit_scopes=sum(r['kind']!='kani'for r in rows),extraction_scopes=0,standard_axioms=['propext','Classical.choice','Quot.sound'],authoritative_delta=0,security_target_established=False,native_source_scope='Frozen4bb selected statement/core closure; Pool excluded from every selected closure.',off_path_pool_note='Older predecessor off-path Pool corpus retained; required Pool release b936275465; no Pool source-parity, bridge or ELF credit.')
 (p/'NLH_AUDIT.json').write_text(json.dumps(report,indent=1)+'\n')
print(json.dumps(dict(validation='PASS',scopes=len(rows),kani=sum(r['kind']=='kani'for r in rows),lean_and_audit=sum(r['kind']!='kani'for r in rows),library_objects=len(first or{}),final='--final'in sys.argv)))
