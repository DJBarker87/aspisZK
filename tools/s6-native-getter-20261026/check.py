#!/usr/bin/env python3
"""Audit native same-box getter evidence, not whole S6/SDK closure."""
from pathlib import Path
import hashlib
import json
import re
import subprocess
import sys

R = Path(__file__).resolve().parents[2]
E = R / 'docs/research/100bit-spend-path-20261013/evidence/s126-current-caller-20261021'
O = E / (sys.argv[1] if len(sys.argv) > 1 else 's6-native-getter-terminal-v1')
sha = lambda b: hashlib.sha256(b).hexdigest()
load = lambda p: json.loads(p.read_text())
packet = load(O / 'packet-pins.json')
assert not packet['binary_files_included']
for name, expected in packet['files'].items():
    p = O / name
    assert p.suffix in ['.json', '.log', '.py', '.rs', '.toml', '.txt']
    assert sha(p.read_bytes()) == expected
for p in Path(__file__).parent.iterdir():
    if p.is_file() and p.suffix in ['.py', '.rs']:
        assert p.read_bytes() == (O / 'tools' / p.name).read_bytes()

binding = load(O / 'v5/binding.json')
plan = load(O / 'v5/plan.json')
assert binding['release_revision'] == '4bb3b3f51e16b4525f1d10336e2b0bcbbd775387'
attribute = binding['derive_attribute'].encode()
assert attribute == b''
assert not binding['proof_only_arbitrary_derives']
for name, expected in binding['original_source_pins'].items():
    original = subprocess.check_output(['git', 'show', binding['release_revision'] + ':' + name], cwd=R)
    assert sha(original) == expected
    if name in binding['proof_only_arbitrary_derives']:
        changed = (O / 'source' / name).read_bytes()
        assert changed.count(attribute) == len(binding['proof_only_arbitrary_derives'][name])
        assert changed.replace(attribute, b'') == original
        assert sha(changed) == binding['files'][name]
    elif name in binding['manifest_changes']:
        changed = (O / 'source' / name).read_bytes()
        patch = binding['manifest_changes'][name]
        assert sha(changed) == patch['after_sha256']
        assert changed + patch['omitted_suffix'].encode() == original
    else:
        assert binding['files'][name] == expected
for name in ['harness/src/lib.rs', 'harness/Cargo.toml', 'Cargo.toml']:
    assert sha((O / 'source' / name).read_bytes()) == binding['files'][name]
assert {p: plan['files'][p] for p in binding['files']} == binding['files']
assert sha((O / 'v5/binding.json').read_bytes()) == plan['files']['binding.json']
assert sha((O / 'v5/nuc.py').read_bytes()) == plan['files']['nuc.py']
proof = (O / 'source/harness/src/lib.rs').read_text()
assert proof == (Path(__file__).parent / 'proofs.rs').read_text()
assert not re.search(r'\b(unsafe|assume|stub|stub_verified)\s*[(\{]', proof)
assert 'Box::new(arbitrary_statement())' in proof
assert 'core::ptr::eq(p, public)' in proof
assert 'core::ptr::eq(lane, &common.lane_transition)' in proof
assert 'let other = Box::new(*statement);' in proof
assert 'assert!(aliases(&statement, other.semantic_public()));' in proof

# Retain and classify failed admission/dependency attempts explicitly.
assert not load(O / 'v1/positive/admission-before-scope.json')['admitted']
assert not (O / 'v1/positive/compile-receipt.json').exists()
for version, missing in [('v2', 'tree.rs'), ('v3', 'glue_gen.rs')]:
    receipt = load(O / version / 'positive/compile-receipt.json')
    assert receipt['exit_status'] != 0 and receipt['swaps'] == 0
    assert 'couldn\'t read' in (O / version / 'positive/compile-stdout.log').read_text()
    assert missing in (O / version / 'positive/compile-stdout.log').read_text()
    assert not (O / version / 'positive/verify-receipt.json').exists()

failed = load(O / 'v4/positive/verify-receipt.json')
assert failed['exit_status'] != 0 and failed['swaps'] == 0
assert 'CBMC timed out' in (O / 'v4/positive/verify-stdout.log').read_text()
assert 'array' in (O / 'v4/positive/loops.txt').read_text()
subprocess.run([sys.executable, str(Path(__file__).parent / 'generate.py'), '--check'], cwd=R, check=True, stdout=subprocess.DEVNULL)
assert not load(O / 'v5/negative/verify-admission.json')['admitted']
reuse = load(O / 'v6/negative/compile-reuse.json')
assert reuse['source_pins_exact'] and reuse['tool_pins_exact'] and not reuse['compiler_replayed']
assert reuse['sha256'] == sha((O / 'v5/negative/compile-receipt.json').read_bytes())
assert reuse['input_sha256'] == sha((O / 'v5/negative/compile-input.json').read_bytes())
assert sha((O / 'v6/nuc.py').read_bytes()) == sha((Path(__file__).parent / 'nuc-negative.py').read_bytes())
summary = {}
for case in ['positive', 'negative']:
    directory = O / ('v5' if case == 'positive' else 'v6') / case
    for phase in ['compile', 'verify']:
        phase_dir = O / 'v5/negative' if case == 'negative' and phase == 'compile' else directory
        receipt = load(phase_dir / (phase + '-receipt.json'))
        inp = load(phase_dir / (phase + '-input.json'))
        assert receipt['source_unchanged'] and receipt['tools_unchanged'] and receipt['swaps'] == 0
        assert inp['source_pins'] == plan['files']
        assert inp['environment']['CARGO_BUILD_JOBS'] == '1'
        assert '-C opt-level=3' in inp['environment']['RUSTFLAGS']
        assert '-C overflow-checks=yes' in inp['environment']['RUSTFLAGS']
        assert not any(x in receipt['command'] for x in ['--no-unwinding-assertions', '--no-memory-safety-checks'])
        cg = receipt['cgroup']
        cap, high = (2 * 2**30, 1536 * 2**20) if case == 'negative' and phase == 'verify' else (4 * 2**30, 3 * 2**30)
        assert cg['memory.max'] == str(cap) and cg['memory.high'] == str(high)
        assert cg['memory.swap.max'] == '0'
        events = dict(line.split() for line in cg['memory.events'].splitlines())
        assert events['oom'] == '0' and events['oom_kill'] == '0'
        assert receipt['exit_status'] == 0 if phase == 'compile' or case == 'positive' else receipt['exit_status'] != 0
        admission = load(phase_dir / (phase + '-admission.json'))
        assert admission['admitted'] and admission['own_scope_included']
    output = (directory / 'verify-stdout.log').read_text()
    summary[case] = {k: receipt[k] for k in ['exit_status', 'wall_seconds', 'peak_rss_kib', 'swaps']}
    if case == 'positive':
        assert 'VERIFICATION:- SUCCESSFUL' in output
        assert '** 2 of 2 cover properties satisfied' in output
        assert '** 0 of 118 failed' in output
    else:
        assert 'VERIFICATION:- FAILED' in output
        assert 'assertion failed: aliases(&statement, other.semantic_public())' in output
        assert 'unwinding assertion loop' not in output
print(json.dumps({'status': 'PASS', 'native_same_box_getters': summary,
                  'no_decoder_or_getter_stubs': True, 'whole_s6_closed': False,
                  'qualification': 'Kani default allocation/native model; actual decoder/SDK/runtime binding retained'}))
