"""Collect original per-attempt evidence and exact stage accounting; no builds."""
from pathlib import Path
import json,hashlib,subprocess,shlex,lzma,re
R=Path(__file__).resolve().parents[2];E=R/'evidence/pv-runjoin58-20261029'
sha=lambda b:hashlib.sha256(b).hexdigest()
receipts=[json.loads(p.read_text()) for p in sorted(E.glob('receipt-*.json'))]
assert [r['attempt'] for r in receipts]==list(range(68800,68900))
records=[dict(attempt=int(p.stem.split('-')[1]),**r) for p in sorted(E.glob('modules-*.json')) for r in json.loads(p.read_text())]
assert len(records)==100
failed=[]
for r in records:
 if r['accepted']:
  assert not any('sorryAx' in a for a in r['axioms'])
  continue
 s=r['source'];ref=r['source_revision']+':'+s['path'];b=subprocess.check_output(['git','show',ref],cwd=R);assert sha(b)==r['source_sha256']
 failed.append(dict(attempt=r['attempt'],module=r['module'],revision=r['source_revision'],path=s['path'],sha256=sha(b),git_blob=subprocess.check_output(['git','rev-parse',ref],cwd=R,text=True).strip()))
(E/'retained-failed-sources.json').write_text(json.dumps(failed,indent=2)+'\n')
files=[dict(path=r[k+'_path'],sha256=r[k+'_sha256']) for r in records for k in ['output','time']]
code='''import sys,json,pathlib,hashlib
x=json.load(sys.stdin);o=[]
for v in x:
 b=pathlib.Path(v['path']).read_bytes();h=hashlib.sha256(b).hexdigest();assert h==v['sha256'];o.append(dict(path=v['path'],sha256=h,text=b.decode()))
print(json.dumps(o))'''
p=subprocess.run(['ssh','dombarker@100.108.41.90','python3 -c '+shlex.quote(code)],input=json.dumps(files),capture_output=True,text=True);assert p.returncode==0,p.stderr
logs=json.loads(p.stdout);assert len(logs)==200
(E/'original-module-logs.json.xz').write_bytes(lzma.compress(json.dumps(logs).encode()))
(E/'original-module-log-manifest.json').write_text(json.dumps([dict(path=x['path'],sha256=x['sha256'],bytes=len(x['text'].encode())) for x in logs],indent=2)+'\n')
for r in receipts:
 assert r['reservation']['allowed'] is True and r['admission_exit']==0 and r['admission_and_launch_same_shell'] and r['cooldown_checked_before_launch']
assert not list(E.glob('refusal-*.json'))
scopes=subprocess.run(['ssh','dombarker@100.108.41.90',"systemctl --user list-units --plain --no-legend --state=running 'pv58-lean-*'"],capture_output=True,text=True);assert scopes.returncode==0 and not scopes.stdout.strip()
summary=dict(attempts=100,accepted=sum(r['accepted'] for r in receipts),rejected=sum(not r['accepted'] for r in receipts),kani=0,IDs=[68800,68899],audit_IDs=[68897,68898,68899],total_host_wall_seconds=sum(r['host_wall_seconds'] for r in receipts),peak_rss_bytes=max(r['peak_rss_bytes'] for r in receipts),swaps=sum(r['swaps'] for r in receipts),guard_sha256=sha((R/'tools/pv-runjoin58-20261029/compile.py').read_bytes()),own_scopes=scopes.stdout,remaining_compiles=0)
(E/'SUMMARY.json').write_text(json.dumps(summary,indent=2)+'\n')
base='c8fb38ee734a84e8cdb4a3f8b8de697fd66195e7';head=subprocess.check_output(['git','rev-parse','HEAD'],cwd=R,text=True).strip();paths=subprocess.check_output(['git','diff','--name-only',base,'HEAD'],cwd=R,text=True).splitlines()
protected=[p for p in paths if any(q in Path(p).name for q in ['PV_RJDec_','PV_OWN','PV_RJQ_']) or p.startswith(('crates/','programs/','tools/r1-cost-probe/'))];assert not protected,protected
links={}
for name in ['PV_RunJoin_PublishSkeleton54','PV_RunJoin_PublishSkeleton57','PV_RunJoin_PublishContext57']:
 p='docs/research/v8-r0-zk-20261009/lean/R1Z/'+name+'.lean';a=subprocess.check_output(['git','show',base+':'+p],cwd=R);b=(R/p).read_bytes();assert a==b;links[p]=sha(b)
(E/'boundaries.json').write_text(json.dumps(dict(entry=base,audit_source_revision=head,branch=subprocess.check_output(['git','branch','--show-current'],cwd=R,text=True).strip(),protected_changes=protected,unchanged_link_files=links,fields_changed=False,links_changed=False,endpoint_P_removed=0,endpoint_P_added=0,endpoint_P_weakened=0,endpoint_P_changed=0,trust_items_changed=False,step4_started=False,fixture_witness_established=False,common_sample_discharged=False,backend_input_link_discharged=False,guard_sha256=summary['guard_sha256']),indent=2)+'\n')
(E/'commits.txt').write_text(subprocess.check_output(['git','log','--oneline',base+'..HEAD'],cwd=R,text=True))
print(json.dumps(summary,indent=2))
