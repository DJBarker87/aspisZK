import hashlib, json, os, re, subprocess, sys
m, sha, ex, start, swap, obj, out, lp = sys.argv[1:9]
t = open(os.path.join(out, 'time.log')).read()
log = open(os.path.join(out, 'lean.log')).read()
def grab(pat):
    r = re.search(pat, t)
    return int(r.group(1)) if r else None
wall = re.search(r'([0-9.]+) real', t)
objp = os.path.join(obj, m + '.olean')
osha = hashlib.sha256(open(objp, 'rb').read()).hexdigest() if int(ex) == 0 and os.path.exists(objp) else None
axioms = [l for l in log.splitlines() if "depends on axioms" in l or "does not depend on any axioms" in l]
errors = [l for l in log.splitlines() if 'error' in l]
bad = [a for a in axioms if re.search(r'sorryAx|\bAxiom\b', a)]
rev = subprocess.run(['git', '-C', out, 'rev-parse', 'HEAD'], capture_output=True, text=True).stdout.strip()
rec = {
  'module': m, 'source': 'docs/research/100bit-spend-path-20261013/lean/%s.lean' % m,
  'source_sha256': sha, 'object_sha256': osha, 'exit_status': int(ex),
  'wall_seconds': float(wall.group(1)) if wall else None,
  'peak_rss_bytes': grab(r'(\d+)\s+maximum resident set size'),
  'process_swap_count': grab(r'(\d+)\s+swaps'),
  'swap_before': swap, 'started_utc': start, 'source_revision_parent': rev,
  'command': ['/usr/bin/time', '-l', '/Users/dominic/.elan/toolchains/leanprover--lean4---v4.32.0/bin/lean',
              '-j1', '-M4400', '-DElab.async=false', '-o', objp, '/tmp/r1-commit-model-20261019-src/%s.lean' % m],
  'lean_path': lp, 'axioms': axioms, 'errors': errors[:40],
}
json.dump(rec, open(os.path.join(out, 'receipt.json'), 'w'), indent=2)
print(json.dumps({k: rec[k] for k in ['module', 'exit_status', 'wall_seconds', 'peak_rss_bytes', 'process_swap_count']}))
print('\n'.join(axioms))
print('\n'.join(errors[:40]))
