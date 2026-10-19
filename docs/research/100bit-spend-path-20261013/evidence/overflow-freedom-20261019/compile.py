#!/usr/bin/env python3
"""Focused local compile with memory admission and immutable attempt receipts."""
import datetime, fcntl, hashlib, json, os, re, subprocess, sys, time
from pathlib import Path
here = Path(__file__).resolve().parent
repo = Path(subprocess.check_output(['git','rev-parse','--show-toplevel'],text=True).strip())
module = sys.argv[1]
if not re.fullmatch(r'R22[A-Za-z0-9]+', module):
    raise SystemExit('Only new R22 modules are permitted by this launcher')
src = here.parent.parent / 'lean' / (module+'.lean')
obj = Path('/tmp/r1-overflow-free-20261019-objects')
obj.mkdir(exist_ok=True)
lean = '/Users/dominic/.elan/toolchains/leanprover--lean4---v4.32.0/bin/lean'
roots = [str(obj)]+here.joinpath('lean_path.txt').read_text().strip().split(':')
def digest(p):
    return hashlib.sha256(Path(p).read_bytes()).hexdigest()
def swap():
    return subprocess.check_output(['sysctl','-n','vm.swapusage'],text=True).strip()
def memory():
    raw = subprocess.check_output(['vm_stat'],text=True)
    size = int(re.search(r'page size of (\d+) bytes',raw).group(1))
    free = sum(int(re.search(r'Pages '+k+r':\s+(\d+)',raw).group(1)) for k in ['free','inactive'])*size
    return free,raw
source = src.read_text()
imports = []
for m in re.findall(r'^import\s+(\S+)',source,re.M):
    found = next((Path(r)/(m.replace('.','/')+'.olean') for r in roots if (Path(r)/(m.replace('.','/')+'.olean')).exists()),None)
    imports.append({'module':m,'object':str(found) if found else None,'sha256':digest(found) if found else None})
fp = hashlib.sha256(json.dumps(imports,sort_keys=True).encode()).hexdigest()
stamp = datetime.datetime.now(datetime.timezone.utc).strftime('%Y%m%dT%H%M%S.%fZ')
attempt = here/'receipts'/(module+'-'+stamp)
attempt.mkdir(parents=True)
cmd = ['/usr/bin/time','-l',lean,'-j1','-M4400','-DElab.async=false','-o',str(obj/(module+'.olean')),str(src)]
r = {'schema':'focused-extractor-proof-packet-v1','module':module,'source':str(src.relative_to(repo)),
     'source_revision':subprocess.check_output(['git','rev-parse','HEAD'],text=True).strip(),
     'source_sha256':digest(src),'deps_fingerprint':fp,'imports':imports,'command':cmd,
     'lean_path':':'.join(roots),'compiler_sha256':digest(lean),'started_utc':stamp,'axioms':[],
     'exit':None,'wall_s':None,'peak_rss_bytes':None,'swap_before':swap(),'swap_after':None}
with open('/tmp/aspis-local-lean.lock','a') as lock:
    fcntl.flock(lock,fcntl.LOCK_EX)
    free,raw = memory()
    (attempt/'vm_stat.txt').write_text(raw)
    r['free_plus_inactive_bytes'] = free
    if free < 10*1024**3:
        r['status'] = 'not_started_memory_gate'
        r['required_free_plus_inactive_bytes'] = 10*1024**3
    else:
        env = dict(os.environ,LEAN_PATH=':'.join(roots))
        start = time.monotonic()
        with (attempt/'out.log').open('w') as out, (attempt/'time.log').open('w') as err:
            p = subprocess.run(cmd,cwd='/tmp',env=env,stdout=out,stderr=err)
        r['wall_s'] = time.monotonic()-start
        r['exit'] = p.returncode
        r['status'] = 'passed' if p.returncode==0 else 'failed'
        out = (attempt/'out.log').read_text()
        timing = (attempt/'time.log').read_text()
        rss = re.search(r'(\d+)\s+maximum resident set size',timing)
        r['peak_rss_bytes'] = int(rss.group(1)) if rss else None
        r['axioms'] = [l for l in out.splitlines() if 'depends on axioms' in l or 'does not depend on any axioms' in l]
        r['errors'] = [l for l in out.splitlines() if ': error' in l]
    r['swap_after'] = swap()
(attempt/'command.json').write_text(json.dumps(r,indent=2)+'\n')
manifest = here/'manifest.json'
man = json.loads(manifest.read_text()) if manifest.exists() else {'schema':'focused-extractor-proof-packet-v1','attempts':[]}
man['attempts'].append(str((attempt/'command.json').relative_to(here)))
manifest.write_text(json.dumps(man,indent=2)+'\n')
print(json.dumps({k:r[k] for k in ['module','status','exit','wall_s','peak_rss_bytes','free_plus_inactive_bytes']}))
raise SystemExit(r['exit'] if r['exit'] is not None else 78)
