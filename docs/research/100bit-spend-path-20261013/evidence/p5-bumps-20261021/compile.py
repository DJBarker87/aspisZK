#!/usr/bin/env python3
"""Focused local compile with memory admission and immutable attempt receipts."""
import datetime, hashlib, json, os, re, subprocess, sys, time
from pathlib import Path
here = Path(__file__).resolve().parent
repo = Path(subprocess.check_output(['git','rev-parse','--show-toplevel'],text=True).strip())
module = sys.argv[1]
if not re.fullmatch(r'[A-Za-z][A-Za-z0-9]*(?:\.[A-Za-z][A-Za-z0-9]*)*', module):
    raise SystemExit('Only simple focused module names are permitted by this launcher')
src = here.parent.parent / 'lean' / (module.replace('.', '/')+'.lean')
package_root = src.parent
if module.startswith(('AspisV8R17.', 'AspisV8R19.')):
    package_root = repo / 'docs/research/v8-full-view-zk-20260912/lean'
    src = package_root / (module.replace('.', '/')+'.lean')
if module.startswith('AspisR1Qm31ArithmeticProbe.'):
    package_root = here.parent.parent / 'lean/extracted-qm31-arithmetic-20261015'
    src = package_root / (module.replace('.', '/')+'.lean')
for prefix, directory in {
    'AspisR1DecodeKFullV10.': 'extracted-decode-k-canonicality-20261018',
    'AspisR1CandidateParser.': '../evidence/lean-candidate-field-parsers-20261014/generated-input',
}.items():
    if module.startswith(prefix):
        package_root = here.parent.parent / 'lean' / directory
        src = package_root / (module.replace('.', '/')+'.lean')
if not src.exists():
    src = here.parent.parent / 'lean-candidates/r22-current-field-wrapping-20261019' / (module+'.lean')
if not src.exists():
    matches = list((here.parent.parent / 'lean').rglob(module+'.lean'))
    if len(matches) == 1:
        src = matches[0]
if '.' not in module:
    package_root = src.parent
obj = Path('/tmp/codex-cx-p5-bumps-20261021-objects')
obj.mkdir(exist_ok=True)
output_object = obj / (module.replace('.', '/')+'.olean')
output_object.parent.mkdir(parents=True, exist_ok=True)
if output_object.is_symlink():
    output_object.unlink()
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
for m in re.findall(r'^(?:public )?import\s+(\S+)',source,re.M):
    found = next((Path(r)/(m.replace('.','/')+'.olean') for r in roots if (Path(r)/(m.replace('.','/')+'.olean')).exists()),None)
    imports.append({'module':m,'object':str(found) if found else None,'sha256':digest(found) if found else None})
fp = hashlib.sha256(json.dumps(imports,sort_keys=True).encode()).hexdigest()
stamp = datetime.datetime.now(datetime.timezone.utc).strftime('%Y%m%dT%H%M%S.%fZ')
attempt = here/'receipts'/(module+'-'+stamp)
attempt.mkdir(parents=True)
cmd = ['/usr/bin/time','-l',lean,'-j1','-M4400','-DElab.async=false','-o',str(output_object),str(src)]
r = {'schema':'focused-extractor-proof-packet-v1','module':module,'source':str(src.relative_to(repo)),
     'cache_overlay_sha256':digest(here/'cache-overlay.json') if (here/'cache-overlay.json').exists() else None,
     'source_revision':subprocess.check_output(['git','rev-parse','HEAD'],text=True).strip(),
     'source_sha256':digest(src),'deps_fingerprint':fp,'imports':imports,'command':cmd,
     'cwd':str(package_root),'lean_path':':'.join(roots),'compiler_sha256':digest(lean),'started_utc':stamp,'axioms':[],
     'exit':None,'wall_s':None,'peak_rss_bytes':None,'swap_before':swap(),'swap_after':None}
lock = Path('/tmp/aspis-local-lean.lock.d')
while True:
    try:
        lock.mkdir()
        break
    except FileExistsError:
        processes = subprocess.run(['pgrep','-x','lean'],capture_output=True,text=True)
        if time.time()-lock.stat().st_mtime > 1800 and processes.returncode != 0:
            try:
                lock.rmdir()
            except OSError:
                pass
        print('Waiting for shared mkdir Lean lock', flush=True)
        time.sleep(15)
try:
    while True:
        processes = subprocess.run(['pgrep','-x','lean'],capture_output=True,text=True)
        active = []
        for pid in processes.stdout.split():
            args = subprocess.run(['ps','-p',pid,'-o','command='],capture_output=True,text=True).stdout
            if '-M4400' in args:
                active.append(args.strip())
        if not active:
            break
        print('Waiting for another capped Lean process', flush=True)
        time.sleep(60)
    free,raw = memory()
    (attempt/'vm_stat.txt').write_text(raw)
    r['free_plus_inactive_bytes'] = free
    r['admission_rule'] = 'mkdir lock and no other lean -M4400 process; revised local-lean.txt 2026-10-20'
    # Fingerprint immediately before execution, after any shared-lock wait.
    imports = []
    for m in re.findall(r'^(?:public )?import\s+(\S+)', source, re.M):
        found = next((Path(root)/(m.replace('.','/')+'.olean') for root in roots
                      if (Path(root)/(m.replace('.','/')+'.olean')).exists()), None)
        imports.append({'module':m,'object':str(found) if found else None,
                        'sha256':digest(found) if found else None})
    r['imports'] = imports
    r['deps_fingerprint'] = hashlib.sha256(json.dumps(imports,sort_keys=True).encode()).hexdigest()
    env = dict(os.environ,LEAN_PATH=':'.join(roots))
    start = time.monotonic()
    with (attempt/'out.log').open('w') as out, (attempt/'time.log').open('w') as err:
        p = subprocess.run(cmd,cwd=str(package_root),env=env,stdout=out,stderr=err)
    r['wall_s'] = time.monotonic()-start
    r['exit'] = p.returncode
    r['status'] = 'passed' if p.returncode==0 else 'failed'
    r['source_sha256_after'] = digest(src)
    r['source_unchanged_during_compile'] = r['source_sha256_after'] == r['source_sha256']
    out = (attempt/'out.log').read_text()
    timing = (attempt/'time.log').read_text()
    rss = re.search(r'(\d+)\s+maximum resident set size',timing)
    r['peak_rss_bytes'] = int(rss.group(1)) if rss else None
    r['axioms'] = re.findall(r"'[^']+' (?:depends on axioms:\s*\[[^\]]*\]|does not depend on any axioms)", out)
    r['errors'] = [l for l in (out+'\n'+timing).splitlines() if ': error' in l or 'error:' in l or 'must be contained' in l]
    r['process_swaps'] = next((int(m.group(1)) for m in [re.search(r'(\d+)\s+swaps',timing)] if m), None)
    r['swap_after'] = swap()
    if r['exit'] == 0:
        r['object_sha256'] = digest(output_object)
        r['object_size_bytes'] = output_object.stat().st_size
finally:
    lock.rmdir()
(attempt/'command.json').write_text(json.dumps(r,indent=2)+'\n')
manifest = here/'manifest.json'
man = json.loads(manifest.read_text()) if manifest.exists() else {'schema':'focused-extractor-proof-packet-v1','attempts':[]}
man['attempts'].append(str((attempt/'command.json').relative_to(here)))
manifest.write_text(json.dumps(man,indent=2)+'\n')
print(json.dumps({k:r[k] for k in ['module','status','exit','wall_s','peak_rss_bytes','free_plus_inactive_bytes']}))
raise SystemExit(r['exit'] if r['exit'] is not None else 78)
