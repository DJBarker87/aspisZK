from pathlib import Path
import json,lzma,re,hashlib,subprocess,shutil
E=Path(__file__).resolve().parent;B='/home/dombarker/project-offloads/codex-cx-row-bridges-20261109'
sha=lambda b:hashlib.sha256(b).hexdigest()
def raw(p):
 return p.read_bytes()if p.exists()else lzma.decompress(p.with_name(p.name+'.xz').read_bytes())
def dump(n,x):(E/n).write_text(json.dumps(x,indent=1)+'\n')
manifest=json.loads((E/'NKY_AUDIT_ROOTS.json').read_text());all_expected=[n for g in manifest['groups']for n in g];results=[];group_rows=[]
allow={'propext','Classical.choice','Quot.sound'};exceptions=[]
for i,expected in enumerate(manifest['groups']):
 p=E/'NKY_audit'/('batch'+str(i))/('proof'+str(i)+'.json');x=json.loads(p.read_text())
 assert [r['root']for r in x['results']]==expected,(i,'root coverage')
 for r in x['results']:
  assert set(r['walked_axioms'])<=allow,(i,r)
  if not r['equal']:
   assert r['root']=='NHC_DecodeModel.decoder_error',r
   exceptions.append(dict(group=i,root=r['root'],raw=r['walked_axioms'],collector=r['collect_axioms'],ruling="(ab')(3), inherited standard-only raw authoritative exception"))
 if x['exit_status']:
  assert any(r['root']=='NHC_DecodeModel.decoder_error'and not r['equal']for r in x['results']),i
 results+=x['results'];group_rows.append(dict(group=i,roots=len(expected),exit=x['exit_status'],wall=x['wall_seconds'],peak_rss_kib=x['peak_rss_kib'],swaps=x['swaps']))
assert len(results)==len(set(all_expected))==len(all_expected)==manifest['total']
scan=[json.loads(l)for l in(E/'NKY_LOADED_scan.jsonl').read_text().splitlines()]
assert all(not r['dangling']and not r['duplicate_owners']and r['imports_match']for r in scan)
assert json.loads((E/'NKY_L077/receipt.json').read_text())['exit_status']==0
fixture=json.loads((E/'NKY_audit/fixtures/fixtures.json').read_text());assert fixture['exit_status']==0 and len(fixture['results'])==8
prior=json.loads((E/'NKY_PREDECESSOR_COMPARISON.json').read_text());assert prior['status']=='PASS'and not prior['mismatches']
# Exact immutable native graph, lock, features and controls for every credited run.
positive={2,5,8,11,15,18,21,24};negative={3,4,6,7,9,10,12,13,16,17,19,20,22,23,25,26};native=[]
for n in sorted(positive|negative):
 a=f'NKY_K{n:03}';r=json.loads((E/a/'receipt.json').read_text());t=raw(E/a/'stdout.log').decode()
 assert (r['exit_status']==0)==(n in positive)
 assert ('VERIFICATION:- SUCCESSFUL'in t)if n in positive else('VERIFICATION:- FAILED'in t)
 assert not any(k in t for k in ['timed out','unwinding assertion','excessive memory consumption'])
 g=json.loads((E/(a+'-graph-check.json')).read_text());lock=json.loads((E/(a+'-lock-check.json')).read_text());assert g['graph_matches_frozen']and lock['unchanged']
 assert not json.loads((E/(a+'-source-check.json')).read_text())['errors']
 f={r['name']:set(r['features'])for r in g['all_features']}
 assert {'default','private-leaf-salts','optimized-terminal','program-build'}<=f['aspis-r1-cost-probe']
 assert {'pool-adapter','private-leaf-salts'}<=f['aspis-r1-cost-probe-program']
 assert {'r0','pool-v1-kernel'}<=f['aspis-statement']
 assert len([x for x in f['aspis-statement']if x.startswith('pool-v1-pair-forest-')])==12
 native.append(dict(attempt=a,positive=n in positive,exit=r['exit_status'],graph=True,lock_unchanged=True,features=True))
# Receipt cap/admission checks are independent of whether the attempted proof passed.
receipts=[]
for p in sorted(E.glob('NKY_[LK][0-9][0-9][0-9]/receipt.json')):
 r=json.loads(p.read_text());a=r['attempt'];ad=json.loads((E/(a+'-admission.json')).read_text())
 assert ad['exit']==0 and ad['reservation']['allowed']is True
 assert r['limits']=={'memory.high':'6442450944','memory.max':'8589934592','memory.swap.max':'0','pids.max':'64'},a
 assert r['env']['CARGO_TARGET_DIR']==B+'/NKY_target',a
 assert r['env']['TMPDIR']==B+'/NKY_tmp',a
 assert int(r['swaps'])==0,a
 assert r['exit_status']not in[124,137],a
 receipts.append(r)
# Final source bytes must match the last successful focused compile, including tools.
latest={r['module']:r for r in receipts if r['kind']=='lean'and r['exit_status']==0}
modules=[]
for m in [r['module']for r in latest.values()]:
 p=E/(m+'.lean')
 if not p.exists():continue
 r=latest[m];key='NKY_generated/'+m.replace('.','/')+'.lean';assert sha(p.read_bytes())==r['source_hashes'][key],m
 modules.append(dict(module=m,source_sha256=sha(p.read_bytes()),attempt=r['attempt']))
# Check all stored compressed diagnostic hashes and immutable source payloads.
pairs=0
for p in E.rglob('*.sha256'):
 expected=p.read_text().split()[0];q=p.with_name(p.name[:-7]);assert sha(raw(q))==expected,str(p);pairs+=1
idx=json.loads((E/'NKY_INPUTS.json').read_text())
for h,r in idx['objects'].items():
 p=E/r['path'];assert sha(p.read_bytes())==r['archive_sha256'];assert sha(lzma.decompress(p.read_bytes()))==h
for p in E.rglob('*.lean'):
 if 'sources'in p.parts:continue
 t=p.read_text();assert not re.search(r'\b(sorry|admit|native_decide)\b|^\s*axiom\s|set_option\s+(maxHeartbeats|maxRecDepth)',t,re.M),str(p)
for p in E.rglob('*'):
 if p.is_file():assert p.stat().st_size<=20_000_000,str(p)
assert not list(E.rglob('__pycache__'))
counts=dict(lean_support_scopes=sum(r['attempt'].startswith('NKY_L')for r in receipts),kani_budget_scopes=sum(r['attempt'].startswith('NKY_K')for r in receipts),extraction=0,lean_limit=80,kani_limit=30)
assert counts['lean_support_scopes']<=80 and counts['kani_budget_scopes']<=30
# Current host free space and retained job size; read-only, never clean a live cache.
code="""from pathlib import Path
import shutil,json,subprocess
p=Path(%r)
print(json.dumps(dict(disk=shutil.disk_usage(p)._asdict(),workspace_bytes=int(subprocess.check_output(['du','-sb',str(p)],text=True).split()[0]),target=str(p/'NKY_target'),tmp=str(p/'NKY_tmp'),retained=True)))
"""%B
r=subprocess.run(['ssh','-o','ControlMaster=no','dombarker@100.108.41.90','python3'],input=code,text=True,capture_output=True);assert r.returncode==0,r.stderr
host=json.loads(r.stdout);assert host['workspace_bytes']<20_000_000_000 and host['disk']['free']>=40_000_000_000;dump('NKY_FINAL_HOST.json',host)
summary=dict(status='PASS_NEXT_LEDGER_GATE',authoritative_delta=0,roots=len(results),new_roots=len(manifest['new_roots']),groups=group_rows,standard_axioms_only=True,raw_collector_exceptions=exceptions,scan=dict(exit=0,modules=len(scan),dangling=0,duplicate_owners=0,import_mismatches=0),fixtures=dict(exit=0,controls=8),predecessor=prior,source_modules=modules,budget=counts,resources=dict(wall_seconds=sum(r['wall_seconds']for r in receipts),peak_rss_kib=max(int(r['peak_rss_kib'])for r in receipts),swaps=0),scope_limits='6G/8G/swap0/tasks64; Lean -M7000; serial',full_raw_replays=1,combined_elaborations=3,incremental_frame_audit_group=30,source_revision=subprocess.check_output(['git','rev-parse','HEAD'],text=True).strip(),trust='Existing P6/D188/Allocator retained; native semantic transport reclassification only; no new runtime/cryptographic item')
dump('NKY_AUDIT.json',summary);dump('NKY_NATIVE_OWNERSHIP.json',dict(results=native,excluded=['K001 pre-Kani validation failure','K014 memcmp unwind failure'],exact_kmx_patch_sha256='bcdf749b78eb6143789500d98d64ec3d407b8a17a6d1290c70c822473e8e9a67'))
dump('NKY_VALIDATION.json',dict(status='PASS',scope_receipts=len(receipts),source_modules=len(modules),compressed_hash_pairs=pairs,immutable_native_payloads=len(idx['objects']),budget=counts,host=host))
x=json.loads((E/'NKY_CLOSED.json').read_text())
for row in x['rows']:row['local_gate']='PASS_NEXT_LEDGER_GATE'
dump('NKY_CLOSED.json',x);x=json.loads((E/'NKY_LEDGER_DELTA.json').read_text());x['gate']='PASS_LOCAL_AUDIT_CREDIT_WAITS_NEXT_LEDGER';dump('NKY_LEDGER_DELTA.json',x)
print(json.dumps(dict(status=summary['status'],roots=len(results),modules=len(scan),budget=counts,peak_rss_kib=summary['resources']['peak_rss_kib'])))
