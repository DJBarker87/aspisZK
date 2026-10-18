from pathlib import Path
import os, sys, re, json, hashlib, subprocess, time, signal

module, frozen, attempt = sys.argv[1:]
source = Path(frozen)
canonical = Path('/tmp') / (module + '.lean')
objects = Path('/tmp/lean432-project-closure')
evidence = Path('/tmp/lean432-root-evidence-20261018') / attempt
evidence.mkdir(parents=True, exist_ok=False)
sha = lambda p: hashlib.sha256(Path(p).read_bytes()).hexdigest()
canonical.write_bytes(source.read_bytes())
(evidence / 'source.lean').write_bytes(source.read_bytes())
prior = Path('/tmp/lean432-preflight-evidence/outer-step-v3/command.txt').read_text()
leanpath = '/tmp/finfield-focused-evidence-20261018/objects:' + re.search(r'LEAN_PATH="([^"]+)"', prior).group(1)
lean = '/Users/dominic/.elan/toolchains/leanprover--lean4---v4.32.0/bin/lean'
obj = objects / (module + '.olean')
cmd = ['/usr/bin/time', '-l', lean, '-j1', '-M4400', '-DElab.async=false', '-o', str(obj), str(canonical)]
env = os.environ.copy()
env['LEAN_PATH'] = leanpath
imports = {}
base = Path('/Users/dominic/ZK/.worktrees/100bit-spend-path')
roots = [Path(x) for x in leanpath.split(':')]
for m in re.findall(r'^import (\S+)', source.read_text(), re.M):
    relative = Path(*m.split('.'))
    found = next((p / relative.with_suffix('.olean') for p in roots if (p / relative.with_suffix('.olean')).is_file()), None)
    if found is None:
        raise RuntimeError('Missing precompiled direct import: ' + m)
    sources = [base / 'docs/research/100bit-spend-path-20261013/lean' / relative.with_suffix('.lean'),
               base / 'docs/research/v8-r0-sem-proof-20261008/lean' / relative.with_suffix('.lean')]
    sf = next((p for p in sources if p.is_file()), None)
    imports[m] = dict(object_path=str(found), object_sha256=sha(found), source_path=str(sf) if sf else None,
                      source_sha256=sha(sf) if sf else None)
swap_before = subprocess.check_output(['sysctl', 'vm.swapusage'], text=True).strip()
record = dict(module=module, frozen_source=str(source), source_sha256=sha(source),
              canonical_source=str(canonical), command=cmd, cwd='/tmp', lean_path=leanpath,
              compiler=lean, compiler_version=subprocess.check_output([lean, '--version'], text=True).strip(),
              source_revision=subprocess.check_output(['git', 'rev-parse', 'HEAD'], cwd=base, text=True).strip(),
              direct_imports=imports, swap_before=swap_before, max_aggregate_lean_rss_bytes=8*1024**3,
              timeout_seconds=300, started_utc=time.strftime('%Y-%m-%dT%H:%M:%SZ', time.gmtime()))
(evidence/'command.json').write_text(json.dumps(record, indent=2)+'\n')
start = time.monotonic()
peak_aggregate = 0
stop_reason = None
with (evidence/'lean.log').open('w') as output:
    proc = subprocess.Popen(cmd, cwd='/tmp', env=env, stdout=output, stderr=subprocess.STDOUT, start_new_session=True)
    try:
        while proc.poll() is None:
            listing = subprocess.check_output(['ps', '-axo', 'rss=,comm='], text=True)
            aggregate = 0
            for line in listing.splitlines():
                parts = line.strip().split(None, 1)
                if len(parts) == 2 and Path(parts[1]).name == 'lean': aggregate += int(parts[0])*1024
            peak_aggregate = max(peak_aggregate, aggregate)
            if aggregate > 8*1024**3: stop_reason='aggregate Lean RSS exceeded 8 GiB'
            if time.monotonic()-start > 300: stop_reason='focused target timeout'
            if stop_reason:
                os.killpg(proc.pid, signal.SIGTERM)
                break
            time.sleep(1)
    except BaseException as controller_exception:
        stop_reason = 'controller interrupted/error: ' + type(controller_exception).__name__
        if proc.poll() is None:
            try: os.killpg(proc.pid, signal.SIGTERM)
            except ProcessLookupError: pass
    try: rc = proc.wait(timeout=10)
    except subprocess.TimeoutExpired:
        os.killpg(proc.pid, signal.SIGKILL)
        rc = proc.wait()
log = (evidence/'lean.log').read_text()
record.update(exit_status=rc, observed_wall_seconds=round(time.monotonic()-start, 2),
              stopped_reason=stop_reason, peak_aggregate_lean_rss_bytes=peak_aggregate,
              swap_after=subprocess.check_output(['sysctl', 'vm.swapusage'], text=True).strip(),
              ended_utc=time.strftime('%Y-%m-%dT%H:%M:%SZ', time.gmtime()), log_sha256=sha(evidence/'lean.log'))
for key, pattern, cast in [('wall_seconds',r'([\d.]+) real\s+[\d.]+ user',float),
                           ('peak_rss_bytes',r'(\d+)\s+maximum resident set size',int),
                           ('process_swap_count',r'(\d+)\s+swaps\b',int)]:
    match=re.search(pattern,log)
    record[key]=cast(match.group(1)) if match else None
record['axiom_reports']=re.findall(r"'([^']+)' depends on axioms: \[(.*?)\]",log,re.S)
if rc == 0 and obj.is_file(): record['object_sha256']=sha(obj)
(evidence/'receipt.json').write_text(json.dumps(record, indent=2)+'\n')
print(json.dumps({k:record.get(k) for k in ['module','exit_status','wall_seconds','peak_rss_bytes','process_swap_count','stopped_reason','source_sha256','object_sha256']},indent=2))
print(log[:12000])
sys.exit(rc)
