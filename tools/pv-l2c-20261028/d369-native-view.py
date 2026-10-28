"""Pin a private native source view; transfer changed files with rsync."""
from pathlib import Path
import hashlib, json, shlex, subprocess
R = Path(__file__).resolve().parents[2]
E = R / 'evidence/pv-l2c-20261028/resume-d369'
HOST = 'dombarker@100.108.41.90'
BASE = '/home/dombarker/project-offloads/codex-pv-integ4-20261027/source'
DEST = '/home/dombarker/project-offloads/codex-pv-l2c-20261028/native-source'
tracked = subprocess.check_output(['git', 'ls-files'], text=True).splitlines()
prefixes = ['crates/' + c + '/' for c in ['aspis-core', 'aspis-statement', 'aspis-prover', 'aspis-r1-cost-probe']]
prefixes += ['docs/research/v8-r0-zk-20261009/' + p + '/' for p in ['refine/writers', 'refine/blockwriters', 'refine/poseidon', 'z4', 'c3/check', 'c3/build']]
files = [p for p in tracked if any(p.startswith(x) for x in prefixes) and (p.endswith(('.rs', '.bin', '.json')) or p.endswith('Cargo.toml'))] + ['Cargo.toml', 'Cargo.lock']
expected = {p: hashlib.sha256((R / p).read_bytes()).hexdigest() for p in files}
scan = "import pathlib,json,hashlib,sys; r=pathlib.Path(sys.argv[1]); files=json.load(sys.stdin); print(json.dumps({p:hashlib.sha256((r/p).read_bytes()).hexdigest() if (r/p).is_file() else None for p in files}))"
def hashes(root):
    p = subprocess.run(['ssh', HOST, 'python3 -c ' + shlex.quote(scan) + ' ' + shlex.quote(root)], input=json.dumps(files), text=True, capture_output=True, check=True)
    return json.loads(p.stdout)
base_before = hashes(BASE)
changed = [p for p in files if base_before[p] != expected[p]]
subprocess.run(['ssh', HOST, 'test ! -e ' + shlex.quote(DEST) + ' && mkdir ' + shlex.quote(DEST) + ' && cp -as ' + shlex.quote(BASE + '/.') + ' ' + shlex.quote(DEST + '/')], check=True)
listing = E / 'native-overlay-files.txt'
listing.write_text('\n'.join(changed) + '\n')
subprocess.run(['rsync', '-rI', '--files-from=' + str(listing), str(R) + '/', HOST + ':' + DEST + '/'], check=True)
actual = hashes(DEST)
assert actual == expected, 'private source hash mismatch'
assert hashes(BASE) == base_before, 'base source changed during view construction'
(E / 'private-native-view.json').write_text(json.dumps(dict(base=BASE, destination=DEST, expected=expected, actual=actual, overlays=changed, base_unchanged=True), indent=2) + '\n')
print('Pinned', len(files), 'files;', len(changed), 'plain rsync overlays')
