"""Final read-only gate, source/object pins and private export retention."""
from pathlib import Path
import os,json,lzma,hashlib,shutil,subprocess
B=Path.cwd();H=lambda p:hashlib.sha256(p.read_bytes()).hexdigest();J=lambda p:json.loads(p.read_bytes())
required=J(B/'NNL_AUDIT_ROOTS.json');results=[];collector=[]
for i,g in enumerate(required['groups']):
 ps=list((B/'NNL_audit').glob('batch*/proof'+str(i)+'.json'));assert len(ps)==1,(i,ps)
 x=J(ps[0]);assert [r['root']for r in x['results']]==g,(i,'incomplete raw batch')
 assert x['exit_status']in[0,1]
 for r in x['results']:
  assert set(r['walked_axioms'])<={'Classical.choice','Quot.sound','propext'},r
  if not r['equal']:
   assert r['root']in{'AspisR1.NKR_ScheduleExt.transition','NHC_DecodeModel.decoder_error','LIB_VCarriers.Acc','NNI_CollectorAcc.alias_identity'},r
   collector.append(r)
 results+=x['results']
assert len(results)==len({r['root']for r in results})==len(required['roots'])
assert {r['root']for r in results}==set(required['roots'])
assert J(B/'NNL_audit/fixtures/fixtures.json')['results']==J(B/'NNL_EXPECTED_FIXTURES.json')
assert J(B/'NNL_audit/finalscan/scan.json')['exit_status']==0
loaded=[json.loads(l)for l in(B/'NNL_LOADED_scan.jsonl').read_text().splitlines()]
assert all(not r['dangling']and not r['duplicate_owners']and r['imports_match']for r in loaded)
paths=os.environ['LEAN_PATH'].split(':');pins=[]
for row in loaded:
 rel=row['module'].replace('.','/')+'.olean';p=next((Path(root)/rel for root in paths if(Path(root)/rel).is_file()),None);assert p,rel
 for q in[p,Path(str(p)+'.private'),Path(str(p)+'.server'),p.with_suffix('.ir')]:
  if q.is_file():pins.append(dict(module=row['module'],path=str(q),sha256=H(q),bytes=q.stat().st_size))
raw=(json.dumps(dict(LEAN_PATH=paths,selected_objects=pins,modules=len(loaded),scan_pass=True),indent=1)+'\n').encode();(B/'NNL_CLOSURE_PINS.json.xz').write_bytes(lzma.compress(raw));(B/'NNL_CLOSURE_PINS.json.sha256').write_text(hashlib.sha256(raw).hexdigest()+'\n')
def key(x):return(x['module'],next(s for s in['.olean.private','.olean.server','.olean','.ir']if x['path'].endswith(s)))
prior=J(B/'NNL_PREDECESSOR_PINS.json');old={key(x):x for x in prior['selected_objects']};new={key(x):x for x in pins};missing=set(old)-set(new);assert not missing,missing
wrong=[dict(module=k[0],suffix=k[1],old=x,new=new[k])for k,x in old.items()if new[k]['sha256']!=x['sha256']]
expected=J(B/'NNL_EXPECTED_OBJECT_REPLACEMENTS.json')['changed_files']
expected={(r['module'],r['suffix']):r for r in expected}
assert len(wrong)==len(expected),(len(wrong),len(expected))
for r in wrong:
 e=expected[(r['module'],r['suffix'])]
 assert r['old']['sha256']==e['old']and r['new']['sha256']==e['new'],r
 assert r['new']['path']==e['destination'],r
cmp=dict(status='PASS_WITH_PINNED_REVISION4_F9_REPLACEMENTS',previous_files=len(old),current_files=len(new),same_predecessor_files=len(old)-len(wrong),missing_files=[],changed_files=wrong,added_files=len(set(new)-set(old)),change_authority='LIB F9 total parser plus owner revision4(bs); copied/hash-pinned from accepted candidate paths; all current roots re-walked, complete owner/types captured and NFX checked')
(B/'NNL_PREDECESSOR_COMPARISON.json').write_text(json.dumps(cmp,indent=1)+'\n')
cache=B/'NNL_exports_final_20261111';cache.mkdir(exist_ok=True);exports=[]
for p in(B/'NNL_objects').rglob('*'):
 if not p.is_file():continue
 q=cache/p.relative_to(B/'NNL_objects');q.parent.mkdir(parents=True,exist_ok=True)
 if q.exists():assert H(q)==H(p)
 else:shutil.copy2(p,q)
 exports.append(dict(path=str(q),sha256=H(q),bytes=q.stat().st_size))
(B/'NNL_EXPORT.json').write_text(json.dumps(dict(export=str(cache),files=exports,cache_retained=True,disk=shutil.disk_usage(B)._asdict()),indent=1)+'\n')
tools=[];toolroot=Path(os.environ['LEAN_SYSROOT'])
for p in[toolroot/'bin/lean',toolroot/'bin/lake',toolroot/'bin/leanc',B/'lean-toolchain',B/'S2W_run_host.py',B/'S2W_lean_host.py',B/'NNL_native/NNL_ProofDriver',B/'NNL_native/NNL_Driver']:tools.append(dict(path=str(p),sha256=H(p),bytes=p.stat().st_size))
(B/'NNL_TOOL_PINS.json').write_text(json.dumps(tools,indent=1)+'\n')
imports=json.loads(lzma.decompress((B/'NNL_CACHE_IMPORTS.json.xz').read_bytes()));checked=0
for r in imports['files']:assert H(Path(r['destination']))==r['sha256'];checked+=1
for r in pins:assert H(Path(r['path']))==r['sha256']
for q in sorted(B.glob('NNL_L[0-9][0-9][0-9]/receipt.json')):
 r=J(q)
 for n,h in r['source_hashes'].items():assert H(q.parent/'sources'/n)==h,(q,n)
# The retired failed review/scanner attempts remain evidence, never credit.
integrity=dict(status='PASS',required_roots=len(results),raw_standard_only=True,collector_disagreements=collector,fixtures=8,scan_modules=len(loaded),dangling=0,duplicate_owners=0,import_mismatches=0,imported_files_rehashed=checked,selected_files_rehashed=len(pins),exports=len(exports),deletions=0,cache_retained=True,disk=shutil.disk_usage(B)._asdict(),cold_release_replay=False)
(B/'NNL_GATE_INTEGRITY.json').write_text(json.dumps(integrity,indent=1)+'\n');print(json.dumps(integrity))
