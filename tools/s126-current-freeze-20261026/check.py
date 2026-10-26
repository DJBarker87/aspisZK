#!/usr/bin/env python3
"""Reconcile existing S6 component evidence with the authoritative release source.

No compiler, solver, extraction, SDK implementation replacement or artifact
rebuild. --write records a fresh source-only packet; default checks it.
"""
import hashlib
import json
from pathlib import Path
import re
import resource
import subprocess
import sys
import time

ROOT = Path(__file__).resolve().parents[2]
BASE = Path('docs/research/100bit-spend-path-20261013')
EVIDENCE = BASE / 'evidence/s126-current-caller-20261021'
OUT = ROOT / EVIDENCE / 's6-current-freeze-reconcile-v1'
OLD = '25866ec331cc7ce27dd9956609c11d32fa8fa58a'
FREEZE = '4bb3b3f51e16b4525f1d10336e2b0bcbbd775387'
RESEARCH = '5619adf619c2d384b7969990e70009e524ca8358'
CORE_DELTA = 'crates/aspis-core/src/state_only_prefix.rs'


def git(*args):
    return subprocess.check_output(['git', *args], cwd=ROOT)


def sha(data):
    return hashlib.sha256(data).hexdigest()


def source(revision, path):
    return git('show', revision + ':' + path)


def inventory(prefix):
    paths = [git('ls-tree', '-r', '--name-only', rev, prefix).decode().splitlines()
             for rev in [OLD, FREEZE]]
    assert paths[0] == paths[1], (prefix, 'file-set change')
    return {path: {'historical_sha256': sha(source(OLD, path)),
                   'release_sha256': sha(source(FREEZE, path))}
            for path in paths[0]}


def function(text, name):
    # Only the four pinned compact lib.rs functions are sliced here. None
    # contains a brace in a string/comment; require one unique declaration.
    starts = list(re.finditer(r'\bfn ' + re.escape(name) + r'\(', text))
    assert len(starts) == 1
    start = starts[0].start()
    cursor = text.index('{', start)
    depth = 1
    end = cursor + 1
    while depth:
        depth += (text[end] == '{') - (text[end] == '}')
        end += 1
    return text[start:end].encode()


def compute():
    statement = inventory('crates/aspis-statement')
    core = inventory('crates/aspis-core')
    assert len(statement) == 84 and len(core) == 89
    assert all(v['historical_sha256'] == v['release_sha256'] for v in statement.values())
    changed = [p for p, v in core.items() if v['historical_sha256'] != v['release_sha256']]
    assert changed == [CORE_DELTA], changed
    a = source(OLD, CORE_DELTA)
    b = source(FREEZE, CORE_DELTA)
    before = b'for coordinate in [7usize, 6] {\n        absorption[coordinate] = QM31::ONE.sub(absorption[coordinate]);\n    }'
    after = b'absorption[7] = QM31::ONE.sub(absorption[7]);\n    absorption[6] = QM31::ONE.sub(absorption[6]);'
    # Verify the complete delta without claiming semantic equivalence here.
    assert a.count(before) == 1 and a.replace(before, after) == b
    caller = 'programs/r1-cost-probe/src/lib.rs'
    caller_a, caller_b = (source(r, caller).decode() for r in [OLD, FREEZE])
    functions = {}
    for name in ['observer', 'error', 'first', 'first_decoded']:
        x, y = (function(s, name) for s in [caller_a, caller_b])
        assert x == y
        functions[name] = {'sha256': sha(x), 'byte_equal': True}
    assert b'#[cfg(not(feature="cu-profiling"))] {None}' in function(caller_b, 'observer')
    assert b'first_decoded(statement.semantic_public(),public_bytes,proof,k)' in function(caller_b, 'first')
    assert b'verifier::tx1(public,public_bytes,proof,k,SolanaDigest,observer()).map_err(error)' in function(caller_b, 'first_decoded')
    cargo = 'programs/r1-cost-probe/Cargo.toml'
    assert source(OLD, cargo) == source(FREEZE, cargo)
    adapter = 'programs/r1-cost-probe/src/r1_pool_adapter_owned.rs'
    adapter_bytes = source(FREEZE, adapter)
    assert b'first_decoded(statement.semantic_public(), &public_data, &proof_data[proof_start..proof_end], data[1] as usize)' in adapter_bytes
    assert subprocess.run(['git', 'cat-file', '-e', OLD + ':' + adapter], cwd=ROOT,
                          stdout=subprocess.DEVNULL, stderr=subprocess.DEVNULL).returncode != 0
    old_pins = {}
    for name in ['s6-outer-native-codec-source-pins.json',
                 's6-outer-native-binding-source-pins.json',
                 's6-native-forest-decoder-source-pins.json',
                 's6-native-parent-total-source-pins.json',
                 's6-native-payment-source-pins.json', 's6-native-late-source-pins.json']:
        old_pins[name] = sha((ROOT / EVIDENCE / name).read_bytes())
    for name in ['s6-outer-native-binding-source-pins.json', 's6-native-forest-decoder-source-pins.json']:
        pin = json.loads((ROOT / EVIDENCE / name).read_text())
        assert pin['file_sha256'][OLD] == sha(source(FREEZE, pin['file']))
    targets = {}
    accepted = json.loads((ROOT / EVIDENCE / 'accepted-targets.json').read_text())['targets']
    for name in ['S6OuterNativeCodecV1', 'S6CurrentNamedForestPortV1']:
        receipt_path = ROOT / EVIDENCE / accepted[name]['receipt']
        receipt = json.loads(receipt_path.read_text())
        lean_path = BASE / 'lean-candidates/s126-caller-boundary-20261021' / (name + '.lean')
        assert receipt['exit_status'] == 0 and receipt['swaps'] == 0
        assert sha((ROOT / lean_path).read_bytes()) == receipt['source_sha256']
        for report in receipt['print_axioms']:
            if 'does not depend on any axioms' in report:
                continue
            match = re.search(r'depends on axioms:\s*\[([^]]*)\]', report, re.S)
            assert match and set(re.findall(r'[A-Za-z_.]+', match[1])) <= {'propext', 'Classical.choice', 'Quot.sound'}
        targets[name] = {
            'source_path': str(lean_path), 'receipt': str(receipt_path.relative_to(ROOT)),
            'receipt_sha256': sha(receipt_path.read_bytes()),
            **{k: receipt[k] for k in ['source_sha256', 'object_sha256', 'exit_status',
                                      'wall_seconds', 'peak_rss_bytes', 'swaps', 'print_axioms']}}
    reviews = {}
    for path in ['design/RELEASE-LEDGER-20261025.md', 'design/PREMISE-LEDGER-20261025.md',
                 'lean/SAP_FrozenSdk.lean', 'lean/SAP_FrozenSource.lean', 'lean/SAP_PrepareOwner.lean']:
        value = source(RESEARCH, path)
        reviews[path] = sha(value)
    ledger = source(RESEARCH, 'design/RELEASE-LEDGER-20261025.md')
    assert FREEZE.encode() in ledger
    sdk = source(RESEARCH, 'lean/SAP_FrozenSdk.lean')
    assert b'(extraction : S2W_DigestExtraction.AeneasExtraction' in sdk
    assert b'(primitiveOwner : Port5Q1_QueryPorts.SessionAPrimitives queryOps)' in sdk
    return {
        'schema': 'focused-extractor-proof-packet-v1',
        'historical_freeze': OLD, 'authoritative_release_source': FREEZE,
        'reviewed_research': RESEARCH, 'script_sha256': sha(Path(__file__).read_bytes()),
        'statement_inventory': statement, 'core_inventory': core, 'core_changed_files': changed,
        'caller_path': caller, 'caller_function_identity': functions,
        'program_cargo_sha256': sha(source(FREEZE, cargo)),
        'current_owned_adapter_sha256': sha(adapter_bytes),
        'owned_adapter_exists_at_historical_freeze': False,
        'reused_packet_pins': old_pins, 'reused_proofs': targets, 'reviewed_source_pins': reviews,
        'closed': ['all tracked statement crate bytes historical-to-release',
                   'observer/error/first/first_decoded body identity historical-to-release',
                   'program Cargo.toml identity historical-to-release'],
        'not_closed': ['whole transitive dependency/toolchain certificate',
                       'actual SDK stage1 extraction binding',
                       'native Box/ownership/initialization/error/cleanup interpretation',
                       'current owned-adapter equivalence to historical adapter',
                       'source lowering to frozen ELF', 'whole S1', 'whole S2', 'whole S6',
                       'per-attempt 100-bit soundness'],
        'qualification': 'Source identity extends selected component source pins only. '
                         'Historical focused proof receipts retain their original tool/import scope. '
                         'SAP sources reviewed read-only; no claim of replaying their proofs. '
                         'The core delta is recorded, not proved here. Release observer None requires cu-profiling disabled.'}


def main():
    start = time.monotonic()
    result = compute()
    checks = []
    for name in ['check-outer-native-codec.py', 'check-named-forest-port.py']:
        path = ROOT / 'tools/s6-full-forest-roundtrip-20261023' / name
        run = subprocess.run([sys.executable, str(path)], cwd=ROOT, capture_output=True, text=True)
        assert run.returncode == 0, run.stderr
        checks.append({'path': str(path.relative_to(ROOT)), 'sha256': sha(path.read_bytes()),
                       'exit_status': run.returncode, 'output': json.loads(run.stdout)})
    result['reused_evidence_checks'] = checks
    if '--write' in sys.argv:
        OUT.mkdir()  # Never replace a contemporaneous packet.
        (OUT / 'manifest.json').write_text(json.dumps(result, indent=2) + '\n')
        for path in result['reviewed_source_pins']:
            target = OUT / 'reviewed-source' / path
            target.parent.mkdir(parents=True, exist_ok=True)
            target.write_bytes(source(RESEARCH, path))
        delta = git('diff', '--no-ext-diff', OLD, FREEZE, '--', CORE_DELTA)
        (OUT / 'core-delta.patch').write_bytes(delta)
        usage = resource.getrusage(resource.RUSAGE_SELF)
        child = resource.getrusage(resource.RUSAGE_CHILDREN)
        factor = 1 if sys.platform == 'darwin' else 1024
        receipt = {'target': 'source-only S6 historical-to-current-freeze reconciliation',
                   'command': [sys.executable, str(Path(__file__).relative_to(ROOT)), '--write'],
                   'exit_status': 0, 'wall_seconds': time.monotonic() - start,
                   'self_peak_rss_bytes': usage.ru_maxrss * factor,
                   'maximum_child_rss_bytes': child.ru_maxrss * factor,
                   'swaps': usage.ru_nswap + child.ru_nswap,
                   'source_revision': git('rev-parse', 'HEAD').decode().strip(),
                   'python': sys.version, 'git': git('--version').decode().strip(),
                   'print_axioms': 'N/A: source/evidence audit; reused Lean reports in manifest',
                   'new_lean_kani_extraction_calls': 0}
        assert receipt['swaps'] == 0
        (OUT / 'receipt.json').write_text(json.dumps(receipt, indent=2) + '\n')
    else:
        assert result == json.loads((OUT / 'manifest.json').read_text())
        for path, expected in result['reviewed_source_pins'].items():
            assert sha((OUT / 'reviewed-source' / path).read_bytes()) == expected
        assert (OUT / 'core-delta.patch').read_bytes() == git('diff', '--no-ext-diff', OLD, FREEZE, '--', CORE_DELTA)
    print(json.dumps({'status': 'PASS', 'statement_files_identical': 84,
                      'core_files': 89, 'core_delta_retained': CORE_DELTA,
                      'caller_functions_identical': 4, 'whole_s6_closed': False,
                      'new_compiler_solver_calls': 0}))


if __name__ == '__main__':
    main()
