#!/usr/bin/env python3
"""Collect Z10 run receipts into evidence-Z10.json (results + per-job time -v)."""
import json, os, re, sys
out = sys.argv[1]
jobs = {}
for f in sorted(os.listdir(out)):
    if not f.endswith('.log') or f == 'build.log':
        continue
    name = f[:-4]
    log = open(os.path.join(out, f)).read()
    t = open(os.path.join(out, name + '.time')).read() if os.path.exists(os.path.join(out, name + '.time')) else ''
    g = lambda pat: (re.search(pat, t) or [None, None])[1]
    rec = {
        'config': (re.search(r'^CONFIG .*$', log, re.M) or [None])[0],
        'result': (re.search(r'^RESULT .*$', log, re.M) or [None])[0],
        'fail_lines': len(re.findall(r'^FAIL ', log, re.M)),
        'kron': {'ok': len(re.findall(r' OK$', log, re.M)), 'deficient': len(re.findall(r'DEFICIENT$', log, re.M)),
                 'ranks': sorted(set(int(x) for x in re.findall(r'rank=(\d+) of', log)))} if 'KRON' in log else None,
        'exit_status': g(r'Exit status: (\d+)'),
        'wall': g(r'Elapsed \(wall clock\) time \(h:mm:ss or m:ss\): (\S+)'),
        'max_rss_kb': g(r'Maximum resident set size \(kbytes\): (\d+)'),
        'swaps': g(r'Swaps: (\d+)'),
    }
    jobs[name] = rec
src = open(os.path.join(out, 'source-sha256.txt')).read().split('\n')
json.dump({'probe': 'Z10', 'source_sha256': [s for s in src if s], 'exits': open(os.path.join(out, 'exits.txt')).read().split('\n'),
           'jobs': jobs}, open(os.path.join(out, 'evidence-Z10.json'), 'w'), indent=1)
print('jobs', len(jobs))
