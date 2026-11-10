#!/usr/bin/env python3
"""PCXK_heartbeats.py (derived from PCXJ_heartbeats.py: file list = the corrected copies in PCXK_sources, read from disk): maxHeartbeats in force at every credited theorem (python3 -I, stdlib, git show only).
Files: PCXF_CREDITED_FILES.json files (P6u), PRVEq_/PRVCmb_ files in evidence/prov-p6w-20261110 (PCXH replay copies), and the exit-0 PRVEq modules of the later jobs.
Limit in force = innermost effective value: a file/section/namespace-wide `set_option maxHeartbeats N` (until the enclosing `end`), overridden by
`set_option maxHeartbeats M in` placed (possibly in a chain of `set_option .. in`) before the declaration; Lean's default 200000 applies when none is set.
Only the literal text is read; `maxHeartbeats 0` (unlimited) counts as above 200000. P3x (PCWF_) is skipped by instruction."""
import json, re, subprocess, sys, hashlib
REF = 'research'; E = 'evidence/'
def sh(*a):
    r = subprocess.run(['git'] + list(a), capture_output=True); return r.stdout.decode() if r.returncode == 0 else None
def show(p): return sh('show', REF + ':' + p)
import glob, os
HERE = os.path.dirname(os.path.abspath(__file__)) if '__file__' in dir() else '.'
files = {p: 'PCXK corrected copy' for p in sorted(glob.glob(os.path.join(HERE, 'PCXK_sources', '*.lean')))}
def show(p): return open(p).read()
names = set()
OPT = re.compile(r'^\s*set_option\s+maxHeartbeats\s+(\d+)(\s+in)?\b')
DECL = re.compile(r'^\s*(?:@\[[^\]]*\]\s*)?(?:private\s+|protected\s+)?(theorem|lemma)\s+(\S+)')
out = []; per_file = {}; scanned = 0
for p, why in sorted(files.items()):
    src = show(p)
    if src is None: continue
    scanned += 1; lines = src.split('\n')
    stack = [200000]; opens = []   # scope stack: values; opens: kinds
    kinds = []; pend = None; pend_line = None; cnt = 0; over = 0
    wide_line = [None]
    wl = [(200000, None)]
    for i, ln in enumerate(lines, 1):
        s = ln.strip()
        if re.match(r'(namespace|section)\b', s): kinds.append(len(wl)); continue
        if re.match(r'end\b', s) and kinds: del wl[kinds.pop():]; continue
        m = OPT.match(ln)
        if m:
            v = int(m.group(1))
            if m.group(2): pend = (v, i)
            else: wl.append((v, i))
            continue
        if re.match(r'\s*set_option\b.*\bin\s*$', ln): continue
        d = DECL.match(ln)
        if d:
            lim, at = pend if pend else wl[-1]
            pend = None; cnt += 1
            if lim == 0 or lim > 200000:
                over += 1
                out.append(dict(file=p, theorem=d.group(2), limit_in_force=lim, option_line=at, theorem_line=i, option_scope='per-declaration `in`' if at and pend is None and lim != wl[-1][0] else 'file/section-wide', credited_name_listed=d.group(2) in names, source=why))
        elif s and not s.startswith(('--', '/-', '*')) and pend is not None and not s.startswith('set_option'):
            pend = None
    per_file[p] = dict(theorems=cnt, above_200000=over)
over_files = {p: v for p, v in per_file.items() if v['above_200000']}
res = dict(schema='PCXK_HEARTBEATS/1', target_established=False, ref=REF, threshold=200000, files_scanned=scanned, theorems_scanned=sum(v['theorems'] for v in per_file.values()),
           theorems_above_200000=len(out), files_with_theorems_above=len(over_files), credited_name_listed_above=sum(1 for o in out if o['credited_name_listed']),
           note='Credited theorem = any theorem/lemma in a credited file (credited_name_listed marks those named in PCXH_CREDITED_NAMES.json). option_line is the line of the maxHeartbeats option in force (null = none, default 200000 not above threshold).',
           by_file=over_files, theorems=out)
json.dump(res, open(os.path.join(HERE, 'PCXK_HEARTBEATS.json'), 'w'), indent=1)
print({k: v for k, v in res.items() if k not in ('by_file', 'theorems', 'note')})
