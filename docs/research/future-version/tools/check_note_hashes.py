#!/usr/bin/env python3
"""Check the source hashes written in the notes against the hashes the host
recorded when it compiled each attempt.

fv_lean.sh prints `sha256  path` of the source as the first line of
receipts/<attempt>/stdout.log. Collect them on the host with:

  cd ~/project-offloads/future-version-20261111/receipts
  for d in */; do h=$(grep -m1 -oE "^[0-9a-f]{64}" $d/stdout.log 2>/dev/null); \
    [ -n "$h" ] && echo "${d%/} $h"; done > receipt-hashes.txt

then, from docs/research/future-version:

  python3 tools/check_note_hashes.py receipt-hashes.txt

A table row is checked when its first cell is an attempt name (PSD-27,
PSA-e-12, LDM-02, ...) and the row carries a hash, either full or abbreviated
as `prefix…suffix`. Exit status 1 if any row disagrees with its receipt.
Rows that list several attempts in one cell are not checked.
"""
import glob
import re
import sys

rec = {}
for line in open(sys.argv[1]):
    attempt, digest = line.split()
    rec[attempt] = digest

ok = bad = unknown = 0
out = []
for path in sorted(glob.glob('*.md')):
    for n, line in enumerate(open(path), 1):
        if not line.startswith('|'):
            continue
        cells = [c.strip() for c in line.strip().strip('|').split('|')]
        attempt = cells[0] if cells else ''
        if not re.fullmatch(r'[A-Za-z]{2,4}(-[A-Za-z0-9]+)*-\d+[a-z]?', attempt):
            continue
        found = re.findall(r'\b([0-9a-f]{8,64})(?:…([0-9a-f]{2,}))?', line)
        found = [(p, s) for p, s in found if re.search(r'[a-f]', p + s)]
        found = [(p, s) for p, s in found if len(p) == 64 or s or '…' in line]
        if not found:
            continue
        if attempt not in rec:
            unknown += 1
            out.append(f'NO RECEIPT HASH {path}:{n} {attempt}')
            continue
        digest = rec[attempt]
        cand = [(p, s) for p, s in found if digest.startswith(p[:8])]
        if not cand:
            bad += 1
            out.append(f'DISAGREE {path}:{n} {attempt} note={found[:2]} receipt={digest}')
            continue
        p, s = cand[0]
        if digest.startswith(p) and digest.endswith(s):
            ok += 1
        else:
            bad += 1
            out.append(f'DISAGREE {path}:{n} {attempt} note={p}…{s} receipt={digest}')

print(f'agree={ok} disagree={bad} no_receipt_hash={unknown}')
print('\n'.join(out))
sys.exit(1 if bad else 0)
