#!/usr/bin/env python3
"""Send one privacy-premise module to env J, snapshot replacements, retain full receipts."""
import subprocess, pathlib, hashlib, json, sys
ROOT=pathlib.Path(__file__).resolve().parents[4]
HERE=pathlib.Path(__file__).resolve().parent
HOST='dombarker@100.108.41.90'
J='/home/dombarker/project-offloads/aspis-joint-20261019'
H='/home/dombarker/project-offloads/r1-privacy-build-integration-20261019'
T='/home/dombarker/project-offloads/aspis-fs-generic-20261006'
m=sys.argv[1].replace('.','/')
src=ROOT/'docs/research/v8-r0-zk-20261009/lean'/f'{m}.lean'
if not src.exists(): src=ROOT/'docs/research/100bit-spend-path-20261013/lean'/f'{m}.lean'
if not src.exists() and m.startswith('R1'):
    src=ROOT/'docs/research/100bit-spend-path-20261013/lean'/f'{m[2:]}.lean'
if not src.exists() and m.startswith('AspisFormal/'):
    src=ROOT/'AspisFormal'/f'{m}.lean'
assert src.exists(), src
def ssh(s): return subprocess.check_output(['ssh',HOST,s],text=True)
existing = '--existing' in sys.argv[2:]
if existing:
    remote_sha=ssh(f'sha256sum {J}/sources/{m}.lean').split()[0]
    assert remote_sha == hashlib.sha256(src.read_bytes()).hexdigest(), 'shared source differs; refusing replacement'
else:
    # Snapshots retained on host; never overwrite the first snapshot.
    ssh(f'mkdir -p {J}/snapshots/codex-cx-builder-ref8-20261021/{m.rsplit("/",1)[0]}; for p in sources/{m}.lean objects/{m}.olean; do if [ -f {J}/$p ]; then dest={J}/snapshots/codex-cx-builder-ref8-20261021/$(basename $p); [ -e "$dest" ] || cp {J}/$p "$dest"; fi; done')
    subprocess.run(['scp','-q',str(src),f'{HOST}:{J}/sources/{m}.lean'],check=True)
script='''import pathlib, hashlib, re, subprocess, json, datetime, time
J=pathlib.Path(JJ); H=pathlib.Path(HH); T=pathlib.Path(TT); m=MM
p=J/'sources'/f'{m}.lean'
imports=re.findall(r'^import (\\S+)',p.read_text(),re.M)
if EXISTING: imports=[x for x in imports if (J/'objects'/(x.replace('.','/')+'.olean')).exists()]
def sha(p): return hashlib.sha256(p.read_bytes()).hexdigest() if p.exists() else 'missing'
fp=hashlib.sha256(';'.join(f'{x}={sha(J/"objects"/(x.replace(".","/")+".olean"))}' for x in sorted(imports)).encode()).hexdigest()[:16]
sent=(H/'evidence/sent.txt').read_text()
used={int(x.split()[2]) for x in sent.splitlines() if len(x.split())>=3}
a=next(n for n in range(9200,9400) if n not in used and not (T/f'evidence/out-{n}.log').exists())
while True:
 r=subprocess.run(['sh','/home/dombarker/project-offloads/codex-cx-builder-ref8-20261021/run-joint.sh',str(a),m,'J','7000','8',fp],capture_output=True,text=True)
 if r.returncode != 78: break
 time.sleep(20)
out=(T/f'evidence/out-{a}.log').read_text() if (T/f'evidence/out-{a}.log').exists() else r.stdout+r.stderr
t=(T/f'evidence/time-{a}.log').read_text() if (T/f'evidence/time-{a}.log').exists() else ''
def tv(pat):
 q=re.search(pat,t); return q.group(1).strip() if q else None
ex=re.search(r'exit=(\\d+)',out)
print(json.dumps(dict(attempt=a,module=m.replace('/','.'),source_sha256=sha(p),deps_fingerprint=fp,source_revision=REV,source_dirty=DIRTY,exit=int(ex.group(1)) if ex else r.returncode,wall=tv(r'Elapsed \\(wall clock\\) time \\(h:mm:ss or m:ss\\): (.+)'),peak_rss_kib=tv(r'Maximum resident set size \\(kbytes\\): (\\d+)'),swaps=tv(r'Swaps: (\\d+)'),axioms=re.findall(r"^'.+' (?:depends on axioms: \\[[^\\]]*\\]|does not depend on any axioms)",out,re.M),errors=[x for x in out.splitlines() if ': error' in x],stdout=out,time_log=t,launcher_stdout=r.stdout,date_utc=datetime.datetime.now(datetime.timezone.utc).isoformat())))
'''
for k,v in [('DIRTY',bool(subprocess.check_output(['git','status','--porcelain'],text=True).strip())),('EXISTING',existing),('JJ',J),('HH',H),('TT',T),('MM',m),('REV',subprocess.check_output(['git','rev-parse','HEAD'],text=True).strip())]: script=script.replace(k,repr(v))
r=subprocess.run(['ssh',HOST,'python3 -'],input=script,capture_output=True,text=True)
if r.returncode: print(r.stderr);sys.exit(r.returncode)
rec=json.loads(r.stdout)
rec['repo_source']=str(src.relative_to(ROOT))
with (HERE/'builder-cont8-attempts.jsonl').open('a') as f:f.write(json.dumps(rec)+'\n')
print(rec['attempt'],rec['module'],'exit',rec['exit'],rec['wall'],rec['peak_rss_kib']); print(rec['stdout'] if rec['exit'] else '\n'.join(rec['axioms']))
sys.exit(0 if rec['exit'] in (0,67) else 1)
