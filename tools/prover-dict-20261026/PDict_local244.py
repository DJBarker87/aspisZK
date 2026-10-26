"""Receipts for small Std-only local proofs, using lake env lean.

This does not launch host scopes, build dependencies, or change infrastructure.
"""
from pathlib import Path
import hashlib, json, os, re, subprocess, sys, time

root = Path(__file__).resolve().parents[2]
attempt = int(sys.argv[1])
module = sys.argv[2]
assert 24400 <= attempt <= 24699 and module.startswith('PDict_')
evidence = root/'docs/research/100bit-spend-path-20261013/evidence/prover-dict-20261026/world244/local'
evidence.mkdir(exist_ok=True)
assert not (evidence/f'{attempt}-receipt.json').exists()
source = root/'docs/research/v8-r0-zk-20261009/lean/R1Z'/f'{module}.lean'
workspace = root/'tools/prover-dict-20261026/lean244'
objects = workspace/'.lake/build/lib/lean'
out = objects/'R1Z'/f'{module}.olean'
out.parent.mkdir(parents=True, exist_ok=True)
raw = source.read_bytes()
(evidence/f'{attempt}.lean.txt').write_bytes(raw)
cmd = ['lake', 'env', 'lean', '-M7000', '-R', str(source.parent.parent), '-o', str(out), str(source)]
environment = dict(os.environ, LEAN_PATH=str(objects))
start = time.monotonic()
result = subprocess.run(['/usr/bin/time','-l',*cmd], cwd=workspace,
                        env=environment, text=True, capture_output=True)
wall = time.monotonic()-start
(evidence/f'out-{attempt}.log').write_text(result.stdout)
(evidence/f'time-{attempt}.log').write_text(result.stderr)
metric = lambda name: int(re.search(r'(\d+)\s+'+re.escape(name), result.stderr)[1])
record = dict(attempt=attempt, target=cmd, module=module,
    source_revision=subprocess.check_output(['git','rev-parse','HEAD'],cwd=root,text=True).strip(),
    source_sha256=hashlib.sha256(raw).hexdigest(), exit_status=result.returncode,
    wall_seconds=wall, peak_rss_bytes=metric('maximum resident set size'),
    swaps=metric('swaps'), print_axioms=result.stdout,
    toolchain=subprocess.check_output(['lake','env','lean','--version'],cwd=workspace,text=True).strip(),
    object_sha256=hashlib.sha256(out.read_bytes()).hexdigest() if result.returncode==0 else None,
    dependencies={str(p.relative_to(objects)):hashlib.sha256(p.read_bytes()).hexdigest()
        for p in objects.rglob('*.olean') if p != out},
    qualification='Small local Std-only proof; no dependency build or capped host scope. '
        'macOS time -l RSS is in bytes. Full stdout includes rejected declarations, '
        'whose sorryAx reports are never accepted.')
(evidence/f'{attempt}-receipt.json').write_text(json.dumps(record,indent=2)+'\n')
print(result.stdout)
print(json.dumps({k:record[k] for k in ['attempt','exit_status','wall_seconds','peak_rss_bytes','swaps']}))
sys.exit(result.returncode)
