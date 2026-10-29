"""One admitted, capped, sequential native scope; refuses fail-closed (D410)."""
from pathlib import Path
import hashlib, json, subprocess, sys, time
D = Path('/home/dombarker/project-offloads/codex-pv-diag-20261029')
label, *args = sys.argv[1:]
assert not (D / f'{label}-receipt.json').exists()
last = D / 'last-refusal.json'
if last.exists():
    assert time.time() - json.loads(last.read_text())['epoch'] >= 180
ad = D / f'admission-{label}.json'
with (D / f'admission-{label}.log').open('a') as f:
    a = subprocess.run(['python3', str(D.parent / 'codex-pv-runjoin-20261026/reservation-existing.py'), str(ad)], stdout=f, stderr=subprocess.STDOUT)
if a.returncode or not ad.exists() or json.loads(ad.read_text()).get('allowed') is not True:
    (D/f'admission-{label}-refused-{int(time.time())}.json').write_bytes(ad.read_bytes() if ad.exists() else b'{}')
    last.write_text(json.dumps(dict(epoch=time.time(), label=label, exit=a.returncode)))
    print('REFUSED', label, a.returncode, flush=True)
    sys.exit(78)
cmd = ['systemd-run', '--user', '--scope', '--quiet', '-p', 'MemoryHigh=6G', '-p', 'MemoryMax=8G', '-p', 'MemorySwapMax=0', '-p', 'TasksMax=64', '/usr/bin/time', '-v', '-o', str(D / f'{label}-time.log'), 'timeout', '900', 'python3', str(D / 'audit.py'), *args]
(D/f'{label}-audit.py').write_bytes((D/'audit.py').read_bytes())
start = time.time()
with (D / f'{label}-output.log').open('w') as f:
    p = subprocess.run(cmd, stdout=f, stderr=subprocess.STDOUT)
receipt = dict(target=args, command=cmd, exit=p.returncode, wall_seconds=time.time()-start, admission_exit=a.returncode, admission_allowed=True, revision=(D/'revision.txt').read_text().strip(), audit_sha256=hashlib.sha256((D/'audit.py').read_bytes()).hexdigest(), print_axioms='N/A: native artifact/source analysis; no Lean theorem')
(D / f'{label}-receipt.json').write_text(json.dumps(receipt, indent=2)+'\n')
print(label, p.returncode, (D / f'{label}-output.log').read_text()[-2000:], flush=True)
sys.exit(p.returncode)
