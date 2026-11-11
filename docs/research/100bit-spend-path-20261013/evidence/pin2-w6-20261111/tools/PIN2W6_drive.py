"""Compile a list of modules into overlay-PIN2-W4 in import order (effective
graph), one Lean process at a time, through PIN2W6_compile.sh.  Source per
PIN2W6_src.source.  Stops at the first failure (never reruns a failed compile
unchanged: a module with a recorded failure for the same source sha is skipped).
usage: python3 -I PIN2W6_drive.py <scan_dir> <list_file> <note_prefix>"""
import sys, os, subprocess, hashlib
from pathlib import Path
sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
import PIN2W6_graph as G, PIN2W6_src as S
G.load(sys.argv[1])
T = [l.strip() for l in open(sys.argv[2]) if l.strip()]
Ts = set(T); order = []; seen = set()
def visit(m):
    if m in seen or m not in Ts: return
    seen.add(m)
    for d in G.imp.get(m, []): visit(d)
    order.append(m)
for m in T: visit(m)
BUILD = Path('/private/tmp/claude-501/-Users-dominic-ZK/3db59790-41f3-4c53-ae90-3fc42a8cab96/scratchpad/w6build'); BUILD.mkdir(exist_ok=True)
W6 = S.W6; status = W6 / 'drive_status.tsv'
prev = [l.split('\t') for l in status.read_text().splitlines()] if status.exists() else []
failed = {(f[0], f[3]) for f in prev if f[1] == 'fail'}
NOTES = dict(l.split('\t', 1) for l in (W6 / 'CHANGE-NOTES.tsv').read_text().splitlines()[1:]) if (W6 / 'CHANGE-NOTES.tsv').exists() else {}
n = 0
for m in order:
    b, note = S.source(m)
    if b is None: print('NO SOURCE', m); open(status, 'a').write(f'{m}\tfail\tno source\t-\n'); break
    h = hashlib.sha256(b).hexdigest()
    if (m, h) in failed: print('skip: earlier failure on same source', m); break
    (BUILD / f'{m}.lean').write_bytes(b)
    r = subprocess.run([str(W6 / 'PIN2W6_compile.sh'), m, f'{sys.argv[3]}; {note}' + (f'; {NOTES[m]}' if m in NOTES else '')], env={**os.environ, 'SRCDIR': str(BUILD)}, capture_output=True, text=True)
    line = r.stdout.strip().split('\n')[0] if r.stdout.strip() else ''
    print(line, flush=True)
    open(status, 'a').write(f'{m}\t{"ok" if r.returncode == 0 else "fail"}\t{line}\t{h}\n')
    n += 1
    if r.returncode != 0: print(r.stdout[-3000:]); sys.exit(1)
print('drive stop; compiled', n)
