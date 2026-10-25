#!/usr/bin/env python3
"""Collect source-only local diagnostics. Does not launch a compiler/solver."""
from pathlib import Path
import hashlib, json, shutil, subprocess

R = Path(__file__).resolve().parents[2]
E = R / 'docs/research/100bit-spend-path-20261013/evidence/s126-current-caller-20261021'
W = Path('/private/tmp/s126-kani-local-diagnostic-20261025-v1')
P = E / 's1-init-local-20261025'
assert not (P/'manifest.json').exists(); P.mkdir(exist_ok=True)
sha = lambda p: hashlib.sha256(p.read_bytes()).hexdigest()
for name in ['release-asset.json', 'archive-inventory.json', 'tool-file-pins.json', 'source-binding.json']:
    shutil.copyfile(W/name, P/name)
for name in ['Cargo.native.toml', 'Cargo.lock', 'src/lib.rs', 'src/sampler.rs', 'src/r1_wire.rs', 'src/claims_write_proofs.rs']:
    target = P/'original-min'/name
    target.parent.mkdir(parents=True, exist_ok=True)
    shutil.copyfile(W/'min'/name, target)
freeze = '25866ec331cc7ce27dd9956609c11d32fa8fa58a'
frozen = subprocess.check_output(['git', 'show', freeze+':crates/aspis-r1-cost-probe/src/r1_semantic.rs'], cwd=R)
(P/'frozen-r1_semantic.rs').write_bytes(frozen)
for rel in ['crates/aspis-core/src/r0/heap.rs']:
    (P/'frozen-heap.rs').write_bytes(subprocess.check_output(['git', 'show', freeze+':'+rel], cwd=R))
binding = json.loads((P/'source-binding.json').read_text())
for row in binding['native_source_files']:
    assert sha(W/row['path']) == row['sha256'], row
    if 'revision' in row:
        data = subprocess.check_output(['git', 'show', row['revision']+':'+row['source']], cwd=R)
        assert hashlib.sha256(data).hexdigest() == row['sha256'], row
rows = []
for a in sorted(E.glob('s1-init-local-compile-v*'), key=lambda p: int(p.name.rsplit('v',1)[1])):
    if not (a/'receipt.json').exists():
        assert (a/'preflight.json').exists(), a
        rows.append({**json.loads((a/'preflight.json').read_text()),'attempt':a.name})
        continue
    receipt = json.loads((a/'receipt.json').read_text())
    inp = json.loads((a/'input.json').read_text())
    for name, key in [('input.json','input_sha256'), ('stdout.log','stdout_sha256'), ('time.log','stderr_time_sha256')]:
        assert sha(a/name) == receipt[key], (a, name)
    assert all(receipt['source_unchanged'].values()) and all(receipt['tools_unchanged'].values())
    assert receipt['swaps'] == 0 and receipt['watchdog_stop'] is None
    assert receipt['host_SSH_operations'] == 0
    for f in (a/'source').rglob('*') if (a/'source').exists() else []:
        if f.is_file() and f.name != 'run.py':
            rel = str(f.relative_to(a/'source'))
            assert sha(f) == inp['source_files'][rel], (a, rel)
    text = (a/'stdout.log').read_text()+'\n'+(a/'time.log').read_text()
    if 'FieldsShape::Primitive with a different ABI' in text: result = 'KANI_LAYOUT_ICE'
    elif 'function pointers and vtable calls are not supported' in text: result = 'KANI_FORMATTING_POINTER_ICE'
    elif 'Cannot determine layout for an Enum with niche encoding' in text: result = 'KANI_UNSUPPORTED_NICHE_FAILURE'
    elif 'Interaction between raw pointers and unions is not yet supported' in text: result = 'KANI_UNSUPPORTED_UNION_FAILURE'
    elif receipt['exit_status'] == 0: result = 'VERIFIED' if receipt['verification_launched'] else 'COMPILED_ONLY'
    else: result = 'SETUP_OR_TOOL_FAILURE'
    rows.append(dict(attempt=a.name, result=result,
        harness=inp['command'][inp['command'].index('--harness')+1],
        source_files=inp['source_files'],
        **{k:receipt[k] for k in ['exit_status','wall_seconds','peak_rss_bytes','aggregate_rss_peak_observed_bytes','swaps','watchdog_stop','verification_launched']},
        receipt_sha256=sha(a/'receipt.json')))
(P/'results.json').write_text(json.dumps(dict(schema='focused-extractor-proof-packet-v1',
    freeze=freeze, attempts=rows, print_axioms='N/A: Rust/Kani diagnostics, no Lean theorem',
    historical_limit='v1-v7 have pinned commands/environment/input hashes and raw logs, but no contemporaneous execution-driver/source snapshots. Do not invent those snapshots or use compiler controls as formal verification.',
    closure='S1 and S6 remain open. No native initializedness closure from codegen or an unsupported-check failure.'), indent=2)+'\n')
files = [p for p in P.rglob('*') if p.is_file()]
for a in E.glob('s1-init-local-compile-v*'):
    files.extend(p for p in a.rglob('*') if p.is_file())
files.extend(p for p in Path(__file__).parent.glob('*.py'))
(P/'manifest.json').write_text(json.dumps(dict(schema='focused-extractor-proof-packet-v1',
    files={str(p.relative_to(R)):sha(p) for p in sorted(files)}), indent=2)+'\n')
print(json.dumps({'attempts':len(rows),'files':len(files),'packet':str(P)}))
