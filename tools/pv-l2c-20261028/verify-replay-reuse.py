"""Read-only h6 dependency/source fingerprint check for reused Stream B replay objects."""
from pathlib import Path
import subprocess,json,shlex,hashlib
R=Path(__file__).resolve().parents[2];E=R/'evidence/pv-l2c-20261028'
rev=json.loads((E/'focused-resolution.json').read_text())['research_revision']
res=json.loads((E/'focused-resolution.json').read_text())['resolved']
integ=json.loads(subprocess.check_output(['git','show',rev+':evidence/pv-replay-20261027/receipts/final-integrity.json']))
expected={r['module'].replace('/','.'):r for r in integ['project_results']}
ext=json.loads((R/'evidence/pv-runjoin20-20261027/external-object-manifest.json').read_text());expected_ext={r['module'].replace('/','.'):r for r in ext}
code='''import pathlib,json,hashlib,sys
H=pathlib.Path('/home/dombarker/project-offloads/codex-pv-runjoin-20261026');e=json.load(open(H/'runjoin24-lean/J.json'));roots=[pathlib.Path(x) for x in e['LEAN_PATH'].split(':')];mods=json.load(sys.stdin);out={}
for m in mods:
 o=next((root/(m.replace('.','/')+'.olean') for root in roots if (root/(m.replace('.','/')+'.olean')).is_file()),None)
 out[m]=dict(path=str(o),realpath=str(o.resolve()),sha256=hashlib.sha256(o.read_bytes()).hexdigest()) if o else None
base=json.load(open('/home/dombarker/project-offloads/r1-privacy-build-integration-20261019/env/J.json'))
print(json.dumps(dict(objects=out,environment=e,base_environment=base)))
'''
p=subprocess.run(['ssh','dombarker@100.108.41.90','python3 -c '+shlex.quote(code)],input=json.dumps(list(res)),text=True,capture_output=True);assert p.returncode==0,p.stderr
actual=json.loads(p.stdout);objects=actual['objects'];roots=[m for m,x in objects.items() if x and '/codex-pv-replay-20261027/' in x['realpath']];seen=set();fail=[];checks=[]
def walk(m):
 if m in seen:return
 seen.add(m);a=objects.get(m)
 if m in expected_ext:
  want=expected_ext[m]['object_sha256'];checks.append(dict(module=m,actual=a['sha256'] if a else None,expected=want,match=bool(a and a['sha256']==want)))
 elif m in expected:
  want=expected[m]['object_sha256'];src=expected[m]['source_sha256'];checks.append(dict(module=m,actual=a['sha256'] if a else None,expected=want,source_selected=res[m].get('sha256'),source_recorded=src,match=bool(a and a['sha256']==want and res[m].get('sha256')==src)))
  for d in res[m].get('imports',[]):walk(d)
 else:fail.append(m)
for m in roots:walk(m)
# Every replay import prefix used by the private overlay selects exactly the recorded object.
# Compare non-path toolchain/executable/config entries with the unchanged base env J.
env=actual['environment'];base=actual['base_environment'];toolchain={k:dict(actual=env[k],base=base.get(k),match=env[k]==base.get(k)) for k in env if k!='LEAN_PATH'}
out=dict(research_revision=rev,authority='h6; coherent replay final-integrity and h4/SCOPE external manifest',reused_replay_roots=roots,transitive_checks=checks,unpinned_in_replay_dependency_fingerprint=fail,environment=env,toolchain=toolchain,import_prefix_object_fingerprint=hashlib.sha256(json.dumps(checks,sort_keys=True).encode()).hexdigest(),all_match=not fail and all(x['match'] for x in checks) and all(x['match'] for x in toolchain.values()),note='Private overlay changes path names only for reused replay closures: every selected transitive object hash must equal the recorded replay object, and toolchain config is unchanged. No replay object is written.')
(E/'replay-cache-h6-check.json').write_text(json.dumps(out,indent=2)+'\n');print('replay roots',len(roots),'transitive',len(checks),'unresolved',fail,'mismatches',[x for x in checks if not x['match']]);assert out['all_match']
