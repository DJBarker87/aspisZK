#!/usr/bin/env python3
"""Audit R68 modeled integration; never certify Rust library refinement."""
import argparse
import hashlib
import json
import re
from pathlib import Path

root = Path(__file__).resolve().parent.parent
repo = root.parents[2]
evidence = root / 'evidence/r68-traversal-library'
base = 'b99b3220a41429afb4cef6bf033c4ff9584ccf32'
targets = ['AspisV8R19/TraversalRuntime', 'AspisV8R19/TraversalLaws',
           'AspisR68Circle/Types', 'AspisR68Circle/Funs', 'AspisV8R19/TraversalCaller']
allowed_axioms = {'propext', 'Classical.choice', 'Quot.sound'}

def sha(path):
    return hashlib.sha256(path.read_bytes()).hexdigest()

def body(text, namespace):
    marker = 'namespace ' + namespace + '\n'
    assert text.count(marker) == 1
    return text.split(marker, 1)[1]

def preflight():
    generated = root / 'evidence/r67-circle-source/eta-extraction/generated/AspisR67Circle'
    expected_imports = {
        'Types': ['AspisV8R19.TraversalRuntime', 'Aeneas.Data.Discriminant'],
        'Funs': ['AspisR68Circle.Types', 'AspisV8R19.TraversalRuntime',
                 'Aeneas.Std.Scalar.WrappingOps.Add', 'Aeneas.Std.Scalar.WrappingOps.Sub',
                 'Aeneas.Std.Array.ArraySlice', 'Aeneas.Std.Core.Convert']}
    for name in ['Types', 'Funs']:
        original = (generated / (name + '.lean')).read_text()
        modeled = (root / 'lean/AspisR68Circle' / (name + '.lean')).read_text()
        assert body(modeled, 'AspisR68Circle') == body(original, 'AspisR67Circle').replace(
            'AspisR67Circle', 'AspisR68Circle'), name + ': changed generated declaration'
        assert re.findall(r'^import (.+)$', modeled, re.M) == expected_imports[name]
    sources = [root / 'lean' / (t + '.lean') for t in targets]
    for path in sources:
        text = path.read_text()
        assert not re.search(r'\b(sorry|admit|axiom)\b', '\n'.join(
            line for line in text.splitlines() if not line.lstrip().startswith('--'))), path
        assert 'External_Template' not in text
    return sources

def metric(log):
    s = log.read_text()
    assert '\tExit status: 0' in s and '\tSwaps: 0' in s
    assert 'error:' not in s and 'sorryAx' not in s
    raw = re.search(r'Elapsed \(wall clock\) time \(h:mm:ss or m:ss\): ([\d:.]+)', s).group(1)
    seconds = sum(float(v) * 60**i for i, v in enumerate(reversed(raw.split(':'))))
    audits = re.findall(r"'([^']+)' (?:depends on axioms: \[([^\]]*)\]|does not depend on any axioms)", s)
    for _, names in audits:
        assert {a.strip() for a in names.split(',') if a.strip()} <= allowed_axioms
    return {'exit': 0, 'swaps': 0, 'wall_seconds': round(seconds, 2),
            'peak_rss_kib': int(re.search(r'Maximum resident set size \(kbytes\): (\d+)', s).group(1)),
            'axioms_audits': {n: [a.strip() for a in v.split(',') if a.strip()] for n, v in audits}}

def main():
    p = argparse.ArgumentParser()
    p.add_argument('--preflight', action='store_true')
    p.add_argument('--record', action='store_true')
    args = p.parse_args()
    sources = preflight()
    if args.preflight:
        print('PASS: exact generated declaration bodies; explicit concrete library models; source refinement OPEN')
        return
    final = evidence / 'final'
    records = json.loads((final / 'metadata.json').read_text())
    assert len(records) == 315
    fresh = records[-5:]
    assert [r['target_name'] for r in fresh] == targets
    for r, src in zip(fresh, sources):
        assert r['source_sha256'] == sha(src) and r['exit'] == 0
        assert r['base_revision'] == base and r['toolchain'] == 'leanprover/lean4:v4.32.0'
        assert r['command'][1:6] == ['env', 'lean', '-j1', '-M4500', '-R']
    resources = json.loads((final / 'resources.json').read_text())
    assert {k: resources[k] for k in ['memory.high', 'memory.max', 'memory.swap.max', 'pids.max']} == {
        'memory.high': str(5*2**30), 'memory.max': str(7*2**30), 'memory.swap.max': '0', 'pids.max': '128'}
    results = {t: metric(final / (Path(t).name + '.log')) for t in targets}
    assert sum(len(r['axioms_audits']) for r in results.values()) == 28
    pins = json.loads((final / 'dependency-pins.json').read_text())
    for src, t in zip(sources, targets):
        assert pins['/home/dombarker/project-offloads/aspis-r57-lean-src-20260929-a/' + t + '.lean'] == sha(src)
    receipt = {
        'base_revision': base, 'results': results, 'cached_targets': 310,
        'compiled_targets': 5, 'new_theorems': 25, 'definition_closure_audits': 3,
        'dependency_pins': len(pins), 'new_axioms': 0,
        'generated_bodies_unchanged_modulo_namespace': True,
        'Rust_library_refinement': False, 'eta_normalization_source_verified': False,
        'guarded_QM31_execution_proved': False, 'circle_execution_proved': False,
        'full_privacy': False, 'full_soundness': False, 'runtime_changed': False,
        'retained_cu': [1497377, 1498764], 'actual_1M_gate_passed': False,
        'first_remaining': 'Relate the actual slice-chain try_fold/any and array.map specializations to these models, including the two pure conversion sites; then prove guarded QM31 multiplication and compose circle/sampler execution.'}
    source_files = sources + [root / 'tools' / n for n in [
        'run_r63_lean.py', 'run_r64_lean.py', 'run_r68_lean.py', 'check_r68_library.py']]
    source_files += [root / 'evidence/r67-circle-source/MANIFEST.json',
                     root / 'evidence/r66-quartic-inverse/MANIFEST.json']
    source_pins = {str(p.relative_to(repo)): sha(p) for p in source_files}
    if args.record:
        (evidence / 'receipt.json').write_text(json.dumps(receipt, indent=2) + '\n')
        (evidence / 'SOURCE_PINS.json').write_text(json.dumps(source_pins, indent=2) + '\n')
        manifest = {str(p.relative_to(evidence)): sha(p) for p in sorted(evidence.rglob('*'))
                    if p.is_file() and p.name != 'MANIFEST.json'}
        (evidence / 'MANIFEST.json').write_text(json.dumps(manifest, indent=2) + '\n')
    assert json.loads((evidence / 'receipt.json').read_text()) == receipt
    assert json.loads((evidence / 'SOURCE_PINS.json').read_text()) == source_pins
    manifest = json.loads((evidence / 'MANIFEST.json').read_text())
    assert set(manifest) == {str(p.relative_to(evidence)) for p in evidence.rglob('*')
                             if p.is_file() and p.name != 'MANIFEST.json'}
    for name, digest in manifest.items():
        assert sha(evidence / name) == digest, name
    print(json.dumps({'audit': 'PASS', 'compiled': 5, 'theorems': 25, 'new_axioms': 0,
                      'source_refinement': 'OPEN', 'artifacts': len(manifest)}, indent=2))

if __name__ == '__main__':
    main()
