"""Compile every ready JF-family module (NDO_JF*, RPz8_JFx_*, JF*) in import
order through PIN2W4_compile.sh, one at a time.  The source is this
directory's sources/<M>.lean when the PIN2 text changed, otherwise the
unchanged release source from research (copied into a scratch build dir).
usage: python3 -I PIN2W4_drive.py <max_modules> [only-prefix]"""
import json, subprocess, sys, os
from pathlib import Path
HERE = Path(__file__).resolve().parent
sys.path.insert(0, str(HERE))
import PIN2W4_ready as R
BUILD = Path(os.environ.get('W4BUILD', '/private/tmp/claude-501/-Users-dominic-ZK/3db59790-41f3-4c53-ae90-3fc42a8cab96/scratchpad/w4build'))
BUILD.mkdir(exist_ok=True)
git = lambda *a: subprocess.run(['git', '-C', '/Users/dominic/ZK', *a], capture_output=True, check=True).stdout
def release_path(m):
    for p in (f'lean/{m}.lean', f'evidence/replay-dry9-20261027/{m}.lean'):
        try: git('cat-file', '-e', f'research:{p}'); return p
        except subprocess.CalledProcessError: pass
    return None
status = HERE / 'drive_status.tsv'
failed = {l.split('\t')[0] for l in status.read_text().splitlines() if '\tfail\t' in l} if status.exists() else set()
limit = int(sys.argv[1]); only = sys.argv[2] if len(sys.argv) > 2 else ''
isjf = lambda m: m.startswith(('NDO_JF', 'RPz8_JFx_', 'JF')) and m.startswith(only)
done = 0
while done < limit:
    todo = [m for m in R.dep if isjf(m) and not R.has('overlay-PIN2-W4', m) and m not in failed and not R.why(m)]
    if not todo: break
    m = sorted(todo)[0]
    src = HERE / 'sources' / f'{m}.lean'
    if src.exists():
        (BUILD / f'{m}.lean').write_bytes(src.read_bytes()); note = 'W4 PIN2 REGEN (generator, PIN2 inputs)'
    else:
        rp = release_path(m)
        if rp is None:
            failed.add(m); open(status, 'a').write(f'{m}\tfail\tno release source\n'); continue
        (BUILD / f'{m}.lean').write_bytes(git('show', f'research:{rp}'))
        note = f'rebuild, release source UNCHANGED {rp} blob {git("rev-parse", "research:" + rp).decode()[:12]}'
    r = subprocess.run([str(HERE / 'PIN2W4_compile.sh'), m, note], env={**os.environ, 'SRCDIR': str(BUILD)}, capture_output=True, text=True)
    print(r.stdout.strip().split('\n')[0], flush=True)
    open(status, 'a').write(f'{m}\t{"ok" if r.returncode == 0 else "fail"}\t{r.stdout.strip().splitlines()[0] if r.stdout.strip() else ""}\n')
    if r.returncode != 0:
        failed.add(m); print(r.stdout[-1500:], flush=True)
    done += 1
print('drive stop; compiled', done)
