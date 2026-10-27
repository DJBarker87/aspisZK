"""Focused env-J compile with private source/object roots; never shared sources."""
from pathlib import Path
import subprocess,json,hashlib,re,sys,time
H=Path('/home/dombarker/project-offloads/codex-pv-op254-20261027')
J=Path('/home/dombarker/project-offloads/aspis-joint-20261019')
T=Path('/home/dombarker/project-offloads/aspis-fs-generic-20261006/evidence')
base=Path('/home/dombarker/project-offloads/r1-privacy-build-integration-20261019')
a=int(sys.argv[1]);module=sys.argv[2]
assert 38500<=a<=38599 and (module.startswith('PV_B1_') or module.startswith('R1Z.ProverRwFull'))
S=H/'lean';O=H/'lean-objects';R=H/'lean-receipts'/str(a)
R.mkdir(parents=True,exist_ok=False);O.mkdir(exist_ok=True)
src=S/(module.replace('.','/')+'.lean');assert src.exists()
# Derive the standing launcher only by source/object root substitution. All
# reservation, ID, no-repeat, lock, timeout and scope behavior remains intact.
launcher=(base/'tools/run-joint.sh').read_text()
old='SRCROOT="$J/sources"; OBJ="$J/objects"'
assert launcher.count(old)==1
# The standing launcher prepends J/objects via run2.py. Preserve that
# namespace priority after adding the private objects root, rather than letting
# a partial earlier cache namespace shadow the complete shared object tree.
env=json.loads((base/'env/J.json').read_text())
env['LEAN_PATH']=str(J/'objects')+':'+env['LEAN_PATH']
private_env=H/'env-J-private.json'
private_env.write_text(json.dumps(env,indent=2)+'\n')
private=launcher.replace(old,f'SRCROOT="{S}"; OBJ="{O}"')
old_env='ENVJ="$H/env/$E.json"'
assert private.count(old_env)==1
private=private.replace(old_env,f'ENVJ="{private_env}"')
(H/'run-private-joint.sh').write_text(private)
paths=[O,J/'objects']+[Path(x) for x in json.loads((base/'env/J.json').read_text())['LEAN_PATH'].split(':')]
deps={}
for name in re.findall(r'^import (\S+)',src.read_text(),re.M):
 p=next((r/(name.replace('.','/')+'.olean') for r in paths if (r/(name.replace('.','/')+'.olean')).exists()),None)
 assert p is not None,('missing dependency',name)
 if name.startswith(('PV_B1_', 'R1Z.ProverRwFull')): assert p.is_relative_to(O),('foreign private object',name,str(p))
 deps[name]={'path':str(p),'sha256':hashlib.sha256(p.read_bytes()).hexdigest()}
fp=hashlib.sha256(json.dumps(dict(deps=deps,environment=dict(env,LEAN_PATH=str(O)+':'+env['LEAN_PATH'])),sort_keys=True).encode()).hexdigest()
submission=dict(attempt=a,module=module,source_sha256=hashlib.sha256(src.read_bytes()).hexdigest(),source_revision=(H/'proof-revision.txt').read_text().strip(),rust_source_revision='ccf87ccecd8e0463a53bbedd0fc995837937dac9',dependencies=deps,deps_fingerprint=fp,private_source_root=str(S),private_object_root=str(O),launcher_original_sha256=hashlib.sha256(launcher.encode()).hexdigest(),launcher_private_sha256=hashlib.sha256(private.encode()).hexdigest(),launcher_delta='private source/object roots and private env with original shared namespace priority; no shared writes',private_environment_sha256=hashlib.sha256(private_env.read_bytes()).hexdigest())
(R/'submission.json').write_text(json.dumps(submission,indent=2)+'\n')
with (R/'reservation.json').open('w') as log:
 pre=subprocess.run(['python3',str(H/'Port13GATE_admission.py')],stdout=log,stderr=subprocess.STDOUT)
admission=json.loads((R/'reservation.json').read_text())
if pre.returncode or admission.get('allowed') is not True:
 (R/'refusal.json').write_text(json.dumps(dict(attempt=a,charged=0,exit=pre.returncode,scope_started=False)))
 sys.exit(78)
start=time.monotonic()
with (R/'launcher.log').open('w') as log:
 p=subprocess.run(['sh',str(H/'run-private-joint.sh'),str(a),module.replace('.','/'),'J','7000','8',fp],stdout=log,stderr=subprocess.STDOUT)
for n,dest in [('out','out.log'),('time','time.log'),('sha','sha.txt')]:
 f=T/f'{n}-{a}.{ "txt" if n=="sha" else "log"}'
 if f.exists():(R/dest).write_bytes(f.read_bytes())
out=(R/'out.log').read_text() if (R/'out.log').exists() else ''
tm=(R/'time.log').read_text() if (R/'time.log').exists() else ''
status=re.findall(r'^exit=(\d+)',out,re.M);status=int(status[-1]) if status else p.returncode
charged=(R/'time.log').exists()
def metric(p):
 m=re.search(p,tm);return m.group(1) if m else None
receipt=dict(**submission,exit=status,launcher_exit=p.returncode,wall_seconds=time.monotonic()-start,gnu_wall=metric(r'Elapsed \(wall clock\) time \(h:mm:ss or m:ss\): (.+)'),peak_rss_kib=metric(r'Maximum resident set size \(kbytes\): (\d+)'),swap=metric(r'Swaps: (\d+)'),print_axioms=re.findall(r"^'[^']+' (?:depends on axioms: \[[^\]]*\]|does not depend on any axioms)",out,re.M),charged=charged)
(R/'receipt.json').write_text(json.dumps(receipt,indent=2)+'\n')
print(json.dumps({k:receipt[k] for k in ['attempt','module','exit','wall_seconds','peak_rss_kib','swap','charged']}),flush=True)
print(out[-6000:] if status else '\n'.join(receipt['print_axioms']),flush=True)
sys.exit(status)
