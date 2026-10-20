#!/usr/bin/env python3
"""One env-J ROM attempt, with branch snapshots and complete receipts."""
import datetime, hashlib, json, pathlib, re, subprocess, sys
A, M = int(sys.argv[1]), sys.argv[2]
assert 8600 <= A <= 8799
root = pathlib.Path(__file__).resolve().parents[2]
src = root / 'lean' / (M.replace('.', '/') + '.lean')
J = '/home/dombarker/project-offloads/aspis-joint-20261019'
T = '/home/dombarker/project-offloads/aspis-fs-generic-20261006'
H = '/home/dombarker/project-offloads/r1-privacy-build-integration-20261019'
host = 'dombarker@100.108.41.90'
rel = M.replace('.', '/')
remote = f'''import pathlib, shutil, hashlib, json, subprocess, re
J=pathlib.Path({J!r}); rel={rel!r}; A={A}
snap=J/'snapshots'/'codex-cx-priv-rom-20261021'
for folder,ext in [('sources','.lean'),('objects','.olean')]:
 p=J/folder/(rel+ext); s=snap/folder/(rel+ext)
 if p.exists() and not s.exists():
  s.parent.mkdir(parents=True,exist_ok=True); shutil.copy2(p,s)
p=J/'sources'/(rel+'.lean'); p.parent.mkdir(parents=True,exist_ok=True)
'''
subprocess.run(['ssh', host, 'python3 -c '+__import__('shlex').quote(remote)],check=True)
subprocess.run(['scp','-q',str(src),f'{host}:{J}/sources/{rel}.lean'],check=True)
imports = re.findall(r'^import (\S+)',src.read_text(),re.M)
code = f'''import pathlib,hashlib,subprocess,json
J=pathlib.Path({J!r}); T=pathlib.Path({T!r})
deps={{m:hashlib.sha256((J/'objects'/(m.replace('.','/')+'.olean')).read_bytes()).hexdigest() for m in {imports!r} if (J/'objects'/(m.replace('.','/')+'.olean')).exists()}}
fp=hashlib.sha256(';'.join(f'{{m}}={{deps[m]}}' for m in sorted(deps)).encode()).hexdigest()[:16]
p=subprocess.run(['sh',{H+'/tools/run-joint.sh'!r},{str(A)!r},{rel!r},'J','7000','7',fp],capture_output=True,text=True)
print(json.dumps({{'deps_fingerprint':fp,'dependency_objects':deps,'launcher_exit':p.returncode,'launcher_stdout':p.stdout,'launcher_stderr':p.stderr,'stdout':(T/'evidence'/('out-{A}.log')).read_text() if (T/'evidence'/('out-{A}.log')).exists() else '', 'time_log':(T/'evidence'/('time-{A}.log')).read_text() if (T/'evidence'/('time-{A}.log')).exists() else ''}}))
'''
p = subprocess.run(['ssh',host,'python3 -c '+__import__('shlex').quote(code)],capture_output=True,text=True,check=True)
r=json.loads(p.stdout); out=r['stdout']; tl=r['time_log']
def tv(pat):
 m=re.search(pat,tl); return m.group(1).strip() if m else None
ex=re.search(r'exit=(\d+)',out)
r.update(attempt=A,module=M,repo_source=str(src.relative_to(pathlib.Path.cwd())),source_sha256=hashlib.sha256(src.read_bytes()).hexdigest(),source_revision=subprocess.check_output(['git','rev-parse','HEAD'],text=True).strip(),source_dirty=bool(subprocess.check_output(['git','status','--porcelain'],text=True)),date_utc=datetime.datetime.now(datetime.timezone.utc).isoformat(),exit=int(ex.group(1)) if ex else r['launcher_exit'],wall=tv(r'Elapsed \(wall clock\) time \(h:mm:ss or m:ss\): (.+)'),peak_rss_kib=tv(r'Maximum resident set size \(kbytes\): (\d+)'),swaps=tv(r'Swaps: (\d+)'),axioms=[' '.join(x.split()) for x in re.findall(r"^('[^']+' (?:depends on axioms: \[[^\]]*\]|does not depend on any axioms))",out,re.M|re.S)],errors=[l for l in out.splitlines() if 'error' in l])
with (root/'r1p-final'/'attempts.jsonl').open('a') as f: f.write(json.dumps(r)+'\n')
print(r['launcher_stdout']); print('attempt',A,'exit',r['exit'])
sys.exit(r['exit'])
