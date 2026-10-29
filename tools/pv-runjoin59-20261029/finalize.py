"""Collect original receipts, source provenance and protected-boundary checks."""
from pathlib import Path
import subprocess,json,hashlib,shlex,lzma
R=Path(__file__).resolve().parents[2];E=R/'evidence/pv-runjoin59-20261029'
sha=lambda b:hashlib.sha256(b).hexdigest()
receipts=[json.loads(p.read_text()) for p in sorted(E.glob('receipt-*.json'))]
records=[dict(attempt=int(p.stem.split('-')[1]),**v) for p in sorted(E.glob('modules-*.json')) for v in json.loads(p.read_text())]
assert len(receipts)==len(records)==12
assert all(69700<=r['attempt']<=69799 for r in receipts)
failed=[]
for v in records:
 if v['accepted']:
  assert all('sorryAx' not in a for a in v['axioms'])
 else:
  ref=v['source_revision']+':'+v['source']['path'];b=subprocess.check_output(['git','show',ref],cwd=R)
  assert sha(b)==v['source_sha256']
  failed.append(dict(attempt=v['attempt'],module=v['module'],source_revision=v['source_revision'],path=v['source']['path'],sha256=sha(b),git_blob=subprocess.check_output(['git','rev-parse',ref],cwd=R,text=True).strip()))
(E/'retained-failed-sources.json').write_text(json.dumps(failed,indent=2)+'\n')
paths=[dict(path=v[k+'_path'],sha256=v[k+'_sha256']) for v in records for k in ['output','time']]
code='''import sys,pathlib,json,hashlib
out=[]
for x in json.load(sys.stdin):
 b=pathlib.Path(x['path']).read_bytes();assert hashlib.sha256(b).hexdigest()==x['sha256'];out.append(dict(**x,text=b.decode()))
print(json.dumps(out))'''
r=subprocess.run(['ssh','dombarker@100.108.41.90','python3 -c '+shlex.quote(code)],input=json.dumps(paths),text=True,capture_output=True);assert r.returncode==0,r.stderr
logs=json.loads(r.stdout);(E/'original-module-logs.json.xz').write_bytes(lzma.compress(json.dumps(logs).encode()))
(E/'original-module-log-manifest.json').write_text(json.dumps([dict(path=v['path'],sha256=v['sha256'],bytes=len(v['text'].encode())) for v in logs],indent=2)+'\n')
for r in receipts:
 assert r['reservation']['allowed'] is True and r['admission_exit']==0 and r['admission_and_launch_same_shell'] and r['cooldown_checked_before_launch']
scope=subprocess.run(['ssh','dombarker@100.108.41.90',"systemctl --user list-units --plain --no-legend --state=running 'pv59-lean-*'"],text=True,capture_output=True);assert scope.returncode==0 and not scope.stdout.strip()
summary=dict(compiles=len(receipts),accepted=sum(v['accepted'] for v in receipts),rejected=sum(not v['accepted'] for v in receipts),attempt_IDs=[v['attempt'] for v in receipts],audit_IDs=[69797,69798,69799],kani=0,remaining_budget=100-len(receipts),available_unallocated_IDs=[69710,69796],uncharged_refusals=[69700],total_host_wall_seconds=sum(v['host_wall_seconds'] for v in receipts),peak_rss_bytes=max(v['peak_rss_bytes'] for v in receipts),swaps=sum(v['swaps'] for v in receipts),guard_sha256=sha((R/'tools/pv-runjoin59-20261029/compile.py').read_bytes()),own_scopes=scope.stdout,stop='Existing checked owner NodeAppend obstruction blocks non-degenerate successful witness for current ContextLinks; owned candidate correction not installed; budget not exhausted')
(E/'SUMMARY.json').write_text(json.dumps(summary,indent=2)+'\n')
base='87d831d8cf898ed771d6838922277437e017a6ae'
links={}
for name in ['PV_RunJoin_PublishSkeleton54','PV_RunJoin_PublishSkeleton57','PV_RunJoin_PublishContext57','PV_RunJoin_SkeletonWitnessGate57']:
 p='docs/research/v8-r0-zk-20261009/lean/R1Z/'+name+'.lean';a=subprocess.check_output(['git','show',base+':'+p],cwd=R);b=(R/p).read_bytes();assert a==b;links[p]=sha(b)
changes=subprocess.check_output(['git','diff','--name-only',base,'HEAD'],cwd=R,text=True).splitlines()
protected=[p for p in changes if any(q in Path(p).name for q in ['PV_RJDec_','PV_OWN','PV_RJQ_','PV_RJN_']) or p.startswith(('crates/','programs/','tools/r1-cost-probe/'))];assert not protected,protected
(E/'boundaries.json').write_text(json.dumps(dict(entry=base,audit_revision=receipts[-1]['source_revision'],collection_revision=subprocess.check_output(['git','rev-parse','HEAD'],cwd=R,text=True).strip(),branch=subprocess.check_output(['git','branch','--show-current'],cwd=R,text=True).strip(),unchanged_link_files=links,protected_changes=protected,fields_changed=False,links_changed=False,endpoint_P_removed=0,endpoint_P_added=0,endpoint_P_weakened=0,endpoint_P_changed=0,model_witness=False,common_sample_discharged=False,backend_input_discharged=False,step4_started=False),indent=2)+'\n')
(E/'commits.txt').write_text(subprocess.check_output(['git','log','--oneline',base+'..HEAD'],cwd=R,text=True))
print(json.dumps(summary,indent=2))
