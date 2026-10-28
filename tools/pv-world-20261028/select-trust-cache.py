"""Select only h6-qualified replay objects for the OsWorld import cone.
Missing/changed dependency objects are rebuilt privately, never papered over.
"""
from pathlib import Path
import hashlib,json,subprocess
R=Path(__file__).resolve().parents[2];E=R/'evidence/pv-world-20261028'
j=json.loads((E/'observation-resolution.json').read_text());p=j['modules'];seen=set()
def visit(m):
 if m in seen or m not in p:return
 seen.add(m)
 for d in p[m]['imports']:visit(d)
visit('R1Z.PV_RunJoin_TrustItems')
manifest=json.loads((E/'replay-project-pins.json').read_text())
records={x['module'].replace('/','.'):x for x in manifest['project_results']}
ext=json.loads((E/'external-object-manifest.json').read_text());external={x['module'].replace('/','.'):x['object_sha256'] for x in ext}
code='''from pathlib import Path
import json,hashlib
D=Path('/home/dombarker/project-offloads/codex-pv-world-20261028');B=D.parent/'codex-pv-replay-20261027'
sha=lambda p:hashlib.sha256(p.read_bytes()).hexdigest()
e=json.loads((D/'env-J.json').read_text());original=json.loads((B/'env/J.json').read_text())
assert e['LEAN_GITHASH']==original['LEAN_GITHASH'] and e['ELAN_TOOLCHAIN']==original['ELAN_TOOLCHAIN']
rows={};missing=[]
for m in ORDER:
 if m not in NEEDED:continue
 x=PROJECT[m];r=RECORDS.get(m);rel=m.replace('.','/')
 own=D/'lean-objects'/(rel+'.olean')
 valid=r is not None and r['source_sha256']==x['sha256'] and r['status'] in ['pass','reused','ok','compiled']
 # Results use exit/status labels; record the actual status below if ineligible.
 if r is not None and r['source_sha256']==x['sha256'] and r['object_sha256']==r.get('expected_object_sha256'):valid=True
 dep_checks=[]
 for d in x['imports']:
  if d in PROJECT:
   selected=rows.get(d);old=RECORDS.get(d)
   ok=selected is not None and old is not None and selected['sha256']==old['object_sha256'] and selected.get('replay_compatible',False)
  else:
   selected=EXTERNAL.get(d);ok=selected is not None
  dep_checks.append(dict(module=d,ok=ok))
  if not ok:valid=False
 if own.exists() and not own.is_symlink():
  h=sha(own);rows[m]=dict(kind='own previously compiled',path=str(own),sha256=h,replay_compatible=r is not None and h==r['object_sha256'] and all(d['ok'] for d in dep_checks));continue
 obj=B/'objects'/(rel+'.olean');src=B/'sources'/(rel+'.lean')
 if not obj.exists() or not src.exists():valid=False
 elif r is not None and (sha(obj)!=r['object_sha256'] or sha(src)!=x['sha256']):valid=False
 if valid:
  own.parent.mkdir(parents=True,exist_ok=True)
  if not own.exists():own.symlink_to(obj)
  else:assert own.is_symlink() and sha(own)==r['object_sha256']
  companions={}
  for suffix in ['.server','.private','.ir']:
   a=obj.with_suffix('.ir') if suffix=='.ir' else Path(str(obj)+suffix)
   t=own.with_suffix('.ir') if suffix=='.ir' else Path(str(own)+suffix)
   if a.exists():
    if not t.exists():t.symlink_to(a)
    companions[suffix]=sha(a)
  rows[m]=dict(kind='h6 replay',replay_compatible=True,path=str(own),source_path=str(src),source_sha256=sha(src),sha256=sha(obj),recorded_object_sha256=r['object_sha256'],dependencies=dep_checks,companions=companions)
 else:
  missing.append(m)
  for q in [own,Path(str(own)+'.server'),Path(str(own)+'.private'),own.with_suffix('.ir')]:
   if q.is_symlink():q.unlink()
print(json.dumps(dict(root='R1Z.PV_RunJoin_TrustItems',toolchain=e['LEAN_GITHASH'],original_LEAN_PATH=original['LEAN_PATH'],selected_LEAN_PATH=e['LEAN_PATH'],effective_prefix='own private prefix; every reused dependency object equal to replay fingerprint',rows=rows,missing=missing)))
'''.replace('ORDER',repr(j['order'])).replace('NEEDED',repr(seen)).replace('PROJECT',repr(p)).replace('RECORDS',repr(records)).replace('EXTERNAL',repr(external))
r=subprocess.run(['ssh','dombarker@100.108.41.90','python3','-'],input=code,text=True,capture_output=True);assert r.returncode==0,r.stderr
out=json.loads(r.stdout);(E/'d372-trust-cache-selection.json').write_text(json.dumps(out,indent=2)+'\n')
print('h6 selected',len(out['rows']),'pending private compile',len(out['missing']));print('next',out['missing'][:5])
