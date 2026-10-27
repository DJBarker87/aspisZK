"""Retain exact per-run scratch patches and verify all snapshotted hashes."""
from pathlib import Path
import subprocess,json,hashlib,shlex,base64,difflib
E=Path(__file__).resolve().parent;B='/home/dombarker/project-offloads/codex-cx-leaf-p6-11-20261027';H='dombarker@100.108.41.90';R='4bb3b3f51e16b4525f1d10336e2b0bcbbd775387'
receipts=[json.loads(p.read_text()) for p in sorted(E.glob('LPm_K*/receipt.json'))]
paths=[r['attempt']+'/sources/'+s for r in receipts for s in r['sources']]
script='import pathlib,json,base64; b=pathlib.Path('+repr(B)+'); print(json.dumps({s:base64.b64encode((b/s).read_bytes()).decode() for s in '+repr(paths)+'}))'
r=subprocess.run(['ssh',H,'python3 -c '+shlex.quote(script)],capture_output=True,text=True,check=True);snapshots=json.loads(r.stdout)
cache={};audit=[]
for rc in receipts:
 patch=[]
 for s,h in rc['source_hashes'].items():
  data=base64.b64decode(snapshots[rc['attempt']+'/sources/'+s]);assert hashlib.sha256(data).hexdigest()==h
  f=s.removeprefix('LPm_src/')
  if f not in cache:
   v=subprocess.run(['git','show',R+':'+f],capture_output=True)
   cache[f]=v.stdout if v.returncode==0 else b''
  old=cache[f]
  if data!=old:
   patch.extend(difflib.unified_diff(old.decode().splitlines(True),data.decode().splitlines(True),fromfile='a/'+f if old else '/dev/null',tofile='b/'+f,n=3))
 p=E/rc['attempt']/'LPm_harness.patch';p.write_text(''.join(patch))
 graph=json.loads((E/(rc['attempt']+'-graph-check.json')).read_text())
 assert graph['exact_frozen_resolved_graph_match'] and graph['package_and_edges_match'] and graph['lock_unchanged']
 audit.append({'attempt':rc['attempt'],'exit':rc['exit_status'],'source_snapshot_hashes_match':True,'frozen_graph_and_lock_match':True,'patch_sha256':hashlib.sha256(p.read_bytes()).hexdigest(),'patch_bytes':p.stat().st_size})
(E/'LPm_PATCH_AUDIT.json').write_text(json.dumps(audit,indent=2)+'\n')
(E/'LPm_harness.patch').write_bytes((E/receipts[-1]['attempt']/'LPm_harness.patch').read_bytes())
print('Audited',len(audit),'Kani patches, graphs and unchanged locks')
