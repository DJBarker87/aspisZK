from pathlib import Path
import json,subprocess
E=Path(__file__).resolve().parent
receipts=[json.loads(p.read_text()) for p in sorted(E.glob('KSB_L*/receipt.json'))]
B='/home/dombarker/project-offloads/codex-cx-kit2-cache-20261027'
C='/home/dombarker/project-offloads/codex-cx-sound-int2-20261025'
program='''from pathlib import Path
import hashlib,json,datetime
B=Path(BASE);C=Path(COHERENT)
sha=lambda p:hashlib.sha256(p.read_bytes()).hexdigest()
scopes={}
for scope in SCOPES:
 p=Path(scope);events=p/'cgroup.events'
 scopes[scope]=events.read_text() if events.exists() else 'gone'
libs={}
for root in [C,C/'objects']:
 for base in ['Aeneas','AeneasMeta']:
  for p in (root/base).rglob('*'):
   if p.is_file() and any(str(p).endswith(x) for x in ['.olean','.olean.private','.olean.server','.ir']):libs[str(p)]=sha(p)
 for p in root.glob('Aeneas.*'):
  if p.is_file():libs[str(p)]=sha(p)
print(json.dumps(dict(utc=datetime.datetime.now(datetime.timezone.utc).isoformat(),cache=str(B),cache_retained=B.exists(),owned_scopes=scopes,runner_matches={n:sha(B/n)==sha(C/n) for n in ['S2W_lean_host.py','S2W_run_host.py']},private_objects={str(p.relative_to(B)):dict(sha256=sha(p),bytes=p.stat().st_size) for p in (B/'KSB_objects').rglob('*.olean')},aeneas_post_audit_objects=libs,failed_funs_object_present=(B/'KSB_objects/KSB_Kit_Funs.olean').exists())))
'''.replace('BASE',repr(B)).replace('COHERENT',repr(C)).replace('SCOPES',repr([r['cgroup'] for r in receipts]))
r=subprocess.run(['ssh','-o','ConnectTimeout=20','dombarker@100.108.41.90','python3 -'],input=program,capture_output=True,text=True)
if r.returncode:raise SystemExit('read-only terminal check failed '+r.stderr)
x=json.loads(r.stdout);mismatches=[]
for receipt in receipts:
 for path,h in receipt['deps_fingerprint']['aeneas_library_objects'].items():
  if x['aeneas_post_audit_objects'].get(path)!=h:mismatches.append(dict(attempt=receipt['attempt'],path=path))
x['prelaunch_aeneas_pin_mismatches']=mismatches
(E/'KSB_terminal_state.json').write_text(json.dumps(x,indent=2)+'\n')
print(json.dumps(dict(cache_retained=x['cache_retained'],scopes=x['owned_scopes'],runner_matches=x['runner_matches'],failed_funs_object_present=x['failed_funs_object_present'],aeneas_pin_mismatches=mismatches)))
