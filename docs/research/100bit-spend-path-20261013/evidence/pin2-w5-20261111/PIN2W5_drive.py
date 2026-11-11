"""Compile the ready W5 nodes (PLAN.json order) through PIN2W5_compile.sh,
one Lean process at a time.  Source: sources/<M>.lean when the PIN2 text
changed, otherwise the unchanged release source (copied to a build dir).
usage: python3 -I PIN2W5_drive.py <max>"""
import json, os, subprocess, sys
from pathlib import Path
H = Path(__file__).resolve().parent
BUILD = Path('/private/tmp/claude-501/-Users-dominic-ZK/3db59790-41f3-4c53-ae90-3fc42a8cab96/scratchpad/w5build'); BUILD.mkdir(exist_ok=True)
OV = Path('/Users/dominic/aspis-lead-infra/l187-closure/overlay-PIN2-W4')
git = lambda *a: subprocess.run(['git', '-C', '/Users/dominic/ZK', *a], capture_output=True, check=True).stdout
status = H / 'drive_status.tsv'
done_ok = {l.split('\t')[0] for l in status.read_text().splitlines() if '\tok\t' in l} if status.exists() else set()
failed = {l.split('\t')[0] for l in status.read_text().splitlines() if '\tfail\t' in l} if status.exists() else set()
plan = json.loads((H / 'PLAN.json').read_text())['ready']
n = 0
for m in plan:
    if n >= int(sys.argv[1]): break
    if m in done_ok: continue
    if m in failed: print('skip after failure of', m); break
    f = H / 'sources' / f'{m}.lean'
    if f.exists(): (BUILD / f'{m}.lean').write_bytes(f.read_bytes()); note = 'W5 PIN2 REGEN (original generator, native-dump values)'
    else: (BUILD / f'{m}.lean').write_bytes(git('show', f'research:lean/{m}.lean')); note = 'rebuild, release source UNCHANGED'
    r = subprocess.run([str(H / 'PIN2W5_compile.sh'), m, note], env={**os.environ, 'SRCDIR': str(BUILD)}, capture_output=True, text=True)
    line = r.stdout.strip().split('\n')[0] if r.stdout.strip() else ''
    print(line, flush=True)
    open(status, 'a').write(f'{m}\t{"ok" if r.returncode == 0 else "fail"}\t{line}\n')
    n += 1
    if r.returncode != 0: print(r.stdout[-2500:]); break
print('drive stop; compiled', n)
