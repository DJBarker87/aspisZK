#!/usr/bin/env python3
"""One focused local Lean attempt; never writes a pre-existing module/cache."""
import hashlib, json, os, pathlib, re, shutil, subprocess, sys, time
HERE = pathlib.Path(__file__).resolve().parent
ROOT = HERE.parents[4]
BASE = ROOT / 'docs/research/100bit-spend-path-20261013'
OBJECTS = pathlib.Path('/tmp/codex-cx-m10-ledger-20261020-objects')
LOCK = pathlib.Path('/tmp/aspis-local-lean.lock.d')
sha = lambda p: hashlib.sha256(pathlib.Path(p).read_bytes()).hexdigest()
module = sys.argv[1]
source = BASE / 'lean' / (module + '.lean')
old = json.loads((BASE / 'evidence/c3-skeleton-20261020/manifest.json').read_text())
prior = [a for a in old['attempts'] if a['exit'] == 0 and a['module'] == 'R1FinalSoundness'][-1]
lean_path = str(OBJECTS) + ':' + prior['lean_path']
imports = []
for name in re.findall(r'^import (\S+)', source.read_text(), re.M):
    paths = [pathlib.Path(d) / (name.replace('.', '/') + '.olean') for d in lean_path.split(':')]
    p = next((p for p in paths if p.exists()), None)
    if p is None:
        raise SystemExit('missing cached direct import: ' + name)
    imports.append({'module': name, 'path': str(p), 'sha256': sha(p)})
fingerprint = hashlib.sha256(json.dumps(imports, sort_keys=True).encode()).hexdigest()
manifest_path = HERE / 'manifest.json'
manifest = json.loads(manifest_path.read_text()) if manifest_path.exists() else {'schema': 'focused-extractor-proof-packet-v1', 'attempts': []}
for a in manifest['attempts']:
    if a['module'] == module and a['source_sha256'] == sha(source) and a['deps_fingerprint'] == fingerprint:
        raise SystemExit('refusing unchanged source+dependencies replay')
number = 1 + sum(a['module'] == module for a in manifest['attempts'])
folder = HERE / f'{module}-{number}'
folder.mkdir(exist_ok=True)
OBJECTS.mkdir(exist_ok=True)
argv = ['/Users/dominic/.elan/toolchains/leanprover--lean4---v4.32.0/bin/lean', '-j1', '-M4400', '-DElab.async=false', '-R', str(BASE/'lean'), '-o', str(OBJECTS/(module+'.olean')), str(source)]
receipt = {'module': module, 'attempt': number, 'argv': argv, 'lean_path': lean_path, 'source_revision': subprocess.check_output(['git', 'rev-parse', 'HEAD'], cwd=ROOT, text=True).strip(), 'source_sha256': sha(source), 'direct_imports': imports, 'deps_fingerprint': fingerprint}
(folder/'command.json').write_text(json.dumps(receipt, indent=2)+'\n')
(folder/'source.lean').write_bytes(source.read_bytes())
def lean_processes():
    # Exact executable name avoids matching agent prompts containing Lean commands.
    p = subprocess.run(['pgrep', '-x', 'lean'], text=True, capture_output=True)
    return p.stdout.splitlines()
while True:
    try:
        LOCK.mkdir()
    except FileExistsError:
        if time.time()-LOCK.stat().st_mtime > 1800 and not lean_processes():
            LOCK.rmdir()
        else:
            print('waiting for shared mkdir lock', flush=True)
            time.sleep(15)
        continue
    if lean_processes():
        LOCK.rmdir()
        print('waiting 60 seconds for existing Lean process', flush=True)
        time.sleep(60)
        continue
    break
try:
    start = time.monotonic()
    with (folder/'lean.log').open('w') as out:
        result = subprocess.run(['/usr/bin/time', '-l', '-o', str(folder/'time.log')] + argv, cwd=ROOT, env={**os.environ, 'LEAN_PATH': lean_path}, stdout=out, stderr=subprocess.STDOUT)
    elapsed = time.monotonic()-start
finally:
    LOCK.rmdir()
log = (folder/'lean.log').read_text()
timing = (folder/'time.log').read_text()
get = lambda pat: int(re.search(pat, timing).group(1)) if re.search(pat, timing) else None
receipt.update({'exit': result.returncode, 'wall_seconds': elapsed, 'peak_rss_bytes': get(r'(\d+)\s+maximum resident set size'), 'swaps': get(r'(\d+)\s+swaps'), 'axioms': re.findall(r"'[^']+' (?:depends on axioms:\s*\[[^]]*\]|does not depend on any axioms)", log), 'log': str((folder/'lean.log').relative_to(ROOT)), 'time': str((folder/'time.log').relative_to(ROOT))})
obj = OBJECTS/(module+'.olean')
if result.returncode == 0:
    receipt['object'] = {'path': str(obj), 'sha256': sha(obj), 'size': obj.stat().st_size}
    (folder/'accepted-source.lean').write_bytes(source.read_bytes())
manifest['attempts'].append(receipt)
manifest_path.write_text(json.dumps(manifest, indent=2)+'\n')
print(json.dumps({k: receipt[k] for k in ['module','attempt','exit','wall_seconds','peak_rss_bytes','swaps','axioms']}, indent=2))
print(log)
sys.exit(result.returncode)
