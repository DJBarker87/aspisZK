import hashlib, json, os, re, subprocess, sys
from pathlib import Path
m, sha, ex, start, swap, obj, out, lp = sys.argv[1:9]
out = Path(out)
t = (out / 'time.log').read_text()
log = (out / 'lean.log').read_text()
def digest(p):
    return hashlib.sha256(Path(p).read_bytes()).hexdigest()
def grab(pat):
    r = re.search(pat, t)
    return int(r.group(1)) if r else None
wall = re.search(r'([0-9.]+) real', t)
objp = Path(obj) / (m + '.olean')
# Lean may wrap an axiom list across lines.
axioms = re.findall(r"'[^']+' (?:depends on axioms:\s*\[[^\]]*\]|does not depend on any axioms)", log)
errors = [l for l in log.splitlines() if 'error' in l]
wt = out.parents[4]
while not (wt / '.git').exists():
    wt = wt.parent
src = wt / 'docs/research/100bit-spend-path-20261013/lean' / (m + '.lean')
imports = re.findall(r'^import\s+(\S+)', src.read_text(), re.M)
pins = []
for dep in imports:
    rel = dep.replace('.', '/') + '.olean'
    found = next((Path(base) / rel for base in lp.split(':') if (Path(base) / rel).exists()), None)
    pins.append({'module': dep, 'object_path': str(found) if found else None,
                 'object_sha256': digest(found) if found else None})
fp = hashlib.sha256(json.dumps(pins, sort_keys=True).encode()).hexdigest()
rev = subprocess.run(['git', '-C', str(wt), 'rev-parse', 'HEAD'], capture_output=True, text=True).stdout.strip()
rec = {
  'module': m, 'source': str(src.relative_to(wt)),
  'source_sha256': sha, 'object_sha256': digest(objp) if int(ex) == 0 and objp.exists() else None,
  'object_size_bytes': objp.stat().st_size if int(ex) == 0 and objp.exists() else None,
  'exit_status': int(ex), 'wall_seconds': float(wall.group(1)) if wall else None,
  'peak_rss_bytes': grab(r'(\d+)\s+maximum resident set size'),
  'process_swap_count': grab(r'(\d+)\s+swaps'),
  'swap_before': swap, 'swap_after': subprocess.run(['sysctl', 'vm.swapusage'], capture_output=True, text=True).stdout.strip(),
  'started_utc': start, 'source_revision_parent': rev,
  'command': ['/usr/bin/time', '-l', '/Users/dominic/.elan/toolchains/leanprover--lean4---v4.32.0/bin/lean',
              '-j1', '-M4400', '-DElab.async=false', '-o', str(objp), '/tmp/r1-commit-model-20261019-src/%s.lean' % m],
  'lock': '/tmp/aspis-local-lean.lock.d', 'lean_path': lp,
  'direct_imports': pins, 'deps_fingerprint': fp, 'axioms': axioms, 'errors': errors,
}
(out / 'receipt.json').write_text(json.dumps(rec, indent=2) + '\n')
print(json.dumps({k: rec[k] for k in ['module', 'exit_status', 'wall_seconds', 'peak_rss_bytes', 'process_swap_count']}))
print('\n'.join(axioms))
print('\n'.join(errors[:40]))
