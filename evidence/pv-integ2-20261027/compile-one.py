"""One private-root call of the existing env-J launcher; no shared sources written."""
from pathlib import Path
import subprocess,sys,json,hashlib,re,shlex,datetime,time
E=Path(__file__).resolve().parent;R=E.parents[1];D='/home/dombarker/project-offloads/codex-pv-integ2-20261027';HOST='dombarker@100.108.41.90';T='/home/dombarker/project-offloads/aspis-fs-generic-20261006/evidence'
a=int(sys.argv[1]);module=sys.argv[2];src=Path(sys.argv[3]).resolve();tally=json.loads((E/'TALLY.json').read_text())
assert 54300<=a<=54599 and a not in tally['used_ids'] and tally['lean_charged']<100
if a>=54597:assert module=='PV_Integ2_CombinedAudit'
tally['used_ids'].append(a);tally['next_unused_id']=a+1;(E/'TALLY.json').write_text(json.dumps(tally,indent=2)+'\n')
O=E/'lean-receipts'/str(a);O.mkdir(parents=True);(O/'source.lean.txt').write_bytes(src.read_bytes())
def ssh(s):return subprocess.run(['ssh',HOST,s],capture_output=True,text=True)
pre=ssh(f'python3 {D}/Port13GATE_admission.py > {D}/admission-{a}.json 2>&1; cat {D}/admission-{a}.json')
(O/'reservation.json').write_text(pre.stdout);gate=json.loads(pre.stdout)
if not gate.get('admitted',False):
 (O/'refusal.json').write_text(json.dumps(dict(attempt=a,module=module,charged=False,exit=pre.returncode))+'\n');print('reservation refused',a,flush=True);sys.exit(78)
rel=module.replace('.','/');dest=f'{D}/sources/{rel}.lean'
ssh('mkdir -p '+shlex.quote(str(Path(dest).parent)))
subprocess.run(['scp','-q',str(src),f'{HOST}:{dest}'],check=True)
imports=re.findall(r'^import\s+(\S+)',src.read_text(),re.M)
code='''from pathlib import Path
import json,hashlib
D=Path(%r);e=json.loads(Path('/home/dombarker/project-offloads/r1-privacy-build-integration-20261019/env/J.json').read_text());roots=[D/'objects']+[Path(x) for x in e['LEAN_PATH'].split(':')];out={}
for n in %r:
 p=next((r/Path(n.replace('.','/')+'.olean') for r in roots if (r/Path(n.replace('.','/')+'.olean')).is_file()),None)
 out[n]=dict(path=str(p),sha256=hashlib.sha256(p.read_bytes()).hexdigest()) if p else None
print(json.dumps(out,sort_keys=True))
'''%(D,imports)
deps=ssh('python3 -c '+shlex.quote(code));assert deps.returncode==0,deps.stderr
(O/'dependencies.json').write_text(deps.stdout);fp=hashlib.sha256(deps.stdout.encode()).hexdigest()
revision=subprocess.check_output(['git','rev-parse','HEAD'],cwd=R,text=True).strip()
# The output must be absent or unlinked from hard-linked inherited cache files.
assert ssh(f'test ! -f {D}/objects/{rel}.olean').returncode==0,'never overwrite a shared/hard-linked object'
start=time.monotonic();launch=ssh(f'{D}/run-joint.sh {a} {rel} J 7000 8 {fp}')
(O/'launcher.log').write_text(launch.stdout+launch.stderr)
for name in ['out','time','sha']:
 ext='txt' if name=='sha' else 'log';r=ssh(f'cat {T}/{name}-{a}.{ext}');
 if r.returncode==0:(O/f'{name}.{ext}').write_text(r.stdout)
if not (O/'out.log').exists():
 (O/'refusal.json').write_text(json.dumps(dict(attempt=a,module=module,charged=False,exit=launch.returncode,reason=launch.stdout+launch.stderr))+'\n');print('launcher refused',a,launch.stdout,flush=True);sys.exit(78)
out=(O/'out.log').read_text();tm=(O/'time.log').read_text();status=int(re.findall(r'^exit=(\d+)',out,re.M)[-1])
axioms=re.findall(r"'[^'\n]+' (?:depends on axioms: \[[^\]]*\]|does not depend on any axioms)",out)
rec=dict(attempt=a,module=module,source=str(src.relative_to(R)),source_sha256=hashlib.sha256(src.read_bytes()).hexdigest(),source_revision=revision,deps_fingerprint=fp,exit=status,wall_client_seconds=time.monotonic()-start,axioms=axioms,limits=dict(MemoryHigh='6G',MemoryMax='8G',MemorySwapMax=0,TasksMax=64,lean_M=7000),reason='missing retained object' if module!='PV_Integ2_CombinedAudit' else 'one combined publication audit')
for key,pattern in [('wall',r'Elapsed \(wall clock\) time.*: (.+)'),('peak_RSS_KiB',r'Maximum resident set size \(kbytes\): (\d+)'),('swap',r'Swaps: (\d+)')]:
 m=re.search(pattern,tm);rec[key]=m[1] if m else None
(O/'receipt.json').write_text(json.dumps(rec,indent=2)+'\n')
tally=json.loads((E/'TALLY.json').read_text());tally['lean_charged']+=1;(E/'TALLY.json').write_text(json.dumps(tally,indent=2)+'\n')
print(json.dumps({k:rec[k] for k in ['attempt','module','exit','wall','peak_RSS_KiB','swap']}),flush=True)
if status:print(out[-5000:])
sys.exit(status)
