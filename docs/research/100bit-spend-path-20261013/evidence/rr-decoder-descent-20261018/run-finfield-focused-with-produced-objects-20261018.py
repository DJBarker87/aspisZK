from pathlib import Path
import os, sys, re, json, hashlib, subprocess, time, signal
module, frozen, attempt = sys.argv[1:]
source = Path(frozen)
canonical = Path('/tmp') / (module + '.lean')
root = Path('/tmp/finfield-focused-evidence-20261018')
evidence = root / attempt
evidence.mkdir(parents=True, exist_ok=False)
sha = lambda p: hashlib.sha256(Path(p).read_bytes()).hexdigest()
canonical.write_bytes(source.read_bytes())
(evidence / 'source.lean').write_bytes(source.read_bytes())
prior = Path('/tmp/lean432-preflight-evidence/outer-step-v3/command.txt').read_text()
leanpath = re.search(r'LEAN_PATH="([^"]+)"', prior).group(1) + ':' + str(Path('/tmp/finfield-focused-evidence-20261018/objects'))
lean = '/Users/dominic/.elan/toolchains/leanprover--lean4---v4.32.0/bin/lean'
objects = root / 'objects'; objects.mkdir(exist_ok=True)
obj = objects / (module + '.olean')
cmd = ['/usr/bin/time', '-l', lean, '-j1', '-M4400', '-DElab.async=false', '-o', str(obj), str(canonical)]
env = os.environ.copy(); env['LEAN_PATH'] = leanpath
imports = {}
for m in re.findall(r'^import (\S+)', source.read_text(), re.M):
    relative = Path(*m.split('.')).with_suffix('.olean')
    roots = [Path(x) for x in leanpath.split(':')]
    found = next((p / relative for p in roots if (p / relative).is_file()), None)
    if found is None: raise RuntimeError('Missing direct import: '+m)
    src_candidates = [Path('/Users/dominic/ZK/AspisFormal/.lake/packages/mathlib')/relative.with_suffix('.lean')]
    sf = next((p for p in src_candidates if p.is_file()), None)
    imports[m] = dict(object_path=str(found), object_sha256=sha(found), source_path=str(sf) if sf else None, source_sha256=sha(sf) if sf else None)
swap_before=subprocess.check_output(['sysctl','vm.swapusage'],text=True).strip()
record=dict(module=module, frozen_source=str(source), source_sha256=sha(source), canonical_source=str(canonical), command=cmd, cwd='/tmp', lean_path=leanpath, compiler=lean, compiler_version=subprocess.check_output([lean,'--version'],text=True).strip(), source_revision=subprocess.check_output(['git','rev-parse','HEAD'],cwd='/Users/dominic/ZK',text=True).strip(), direct_imports=imports, swap_before=swap_before, max_aggregate_lean_rss_bytes=8*1024**3, timeout_seconds=300, started_utc=time.strftime('%Y-%m-%dT%H:%M:%SZ',time.gmtime()))
(evidence/'command.json').write_text(json.dumps(record,indent=2)+'\n')
start=time.monotonic(); peak=0; stop=None
with (evidence/'lean.log').open('w') as out:
 p=subprocess.Popen(cmd,cwd='/tmp',env=env,stdout=out,stderr=subprocess.STDOUT,start_new_session=True)
 try:
  while p.poll() is None:
   listing=subprocess.check_output(['ps','-axo','rss=,comm='],text=True); agg=0
   for line in listing.splitlines():
    parts=line.strip().split(None,1)
    if len(parts)==2 and Path(parts[1]).name=='lean': agg+=int(parts[0])*1024
   peak=max(peak,agg)
   if agg>8*1024**3: stop='aggregate Lean RSS exceeded 8 GiB'
   if time.monotonic()-start>300: stop='focused target timeout'
   if stop: os.killpg(p.pid,signal.SIGTERM); break
   time.sleep(1)
 except BaseException as e:
  stop='controller exception: '+type(e).__name__
  if p.poll() is None:
   try: os.killpg(p.pid,signal.SIGTERM)
   except ProcessLookupError: pass
 try: rc=p.wait(timeout=10)
 except subprocess.TimeoutExpired: os.killpg(p.pid,signal.SIGKILL); rc=p.wait()
log=(evidence/'lean.log').read_text(); record.update(exit_status=rc,observed_wall_seconds=round(time.monotonic()-start,2),stopped_reason=stop,peak_aggregate_lean_rss_bytes=peak,swap_after=subprocess.check_output(['sysctl','vm.swapusage'],text=True).strip(),ended_utc=time.strftime('%Y-%m-%dT%H:%M:%SZ',time.gmtime()),log_sha256=sha(evidence/'lean.log'))
for key,pat,cast in [('wall_seconds',r'([\d.]+) real\s+[\d.]+ user',float),('peak_rss_bytes',r'(\d+)\s+maximum resident set size',int),('process_swap_count',r'(\d+)\s+swaps\b',int)]:
 m=re.search(pat,log); record[key]=cast(m.group(1)) if m else None
record['axiom_reports']=re.findall(r"'([^']+)' depends on axioms: \[(.*?)\]",log,re.S)
if rc==0 and obj.is_file(): record['object_sha256']=sha(obj)
(evidence/'receipt.json').write_text(json.dumps(record,indent=2)+'\n')
print(json.dumps({k:record.get(k) for k in ['module','exit_status','wall_seconds','peak_rss_bytes','process_swap_count','stopped_reason','source_sha256','object_sha256']},indent=2)); print(log[:12000]); sys.exit(rc)
