#!/usr/bin/env python3
"""Source-only preflight. Never launches Lean, extraction, Rust, or a host job."""
import hashlib
import json
from pathlib import Path
import re
import resource
import subprocess
import time

R = Path(__file__).resolve().parents[2]
L = R / 'docs/research/100bit-spend-path-20261013/lean'
E = R / 'evidence/port19rest-20261024'
BASE = '3d18d36112'
IDS = {6, 9, 10, 11, 12, 19}

def git(*args):
    return subprocess.check_output(['git', *args], cwd=R)

def pin(p):
    data = p.read_bytes()
    return {'path': str(p.relative_to(R)), 'sha256': hashlib.sha256(data).hexdigest(),
            'bytes': len(data)}

def read_json(p):
    assert p.stat().st_size <= 5_000_000, 'large derived JSON: hash/size only'
    return json.loads(p.read_text())

def rust_item(text, marker):
    # These six retained markers contain no braced strings/comments; compare
    # exact historical span hashes, not a heuristic claim about Rust semantics.
    a = text.index(marker)
    b = text.index('{', a)
    depth, end = 1, b + 1
    while depth:
        depth += (text[end] == '{') - (text[end] == '}')
        end += 1
    return text[a:end], text[:a].count('\n') + 1

def main():
    started = time.monotonic()
    assert git('branch', '--show-current').decode().strip() == 'codex/cx-port19rest-20261024'
    base = git('rev-parse', BASE).decode().strip()
    inventory = R / 'evidence/ports3-20261023/source-body-inventory.json'
    rows = []
    for row in read_json(inventory)['rows']:
        if row['op'] not in IDS:
            continue
        p = R / row['path']
        assert p.read_bytes() == git('show', f'{base}:{row["path"]}')
        body, line = rust_item(p.read_text(), row['marker'])
        assert hashlib.sha256(body.encode()).hexdigest() == row['current_body_sha256']
        rows.append({**row, 'line_at_assigned_base': line, 'complete_body': body,
                     'status': 'native effect producer not established'})
    assert {r['op'] for r in rows} == IDS

    constructor_meta_path = R / 'evidence/ports3-20261023/source-normalization.json'
    constructor_meta = read_json(constructor_meta_path)
    constructor_emission = R / constructor_meta['constructor_emission']
    assert pin(constructor_emission)['sha256'] == constructor_meta['constructor_emission_sha256']
    assert constructor_meta['constructor_instruction_normalization'] is True

    emissions = []
    for name in ['pending', 'query', 'geometry', 'finish', 'flush']:
        p = R / f'evidence/ports3-20261023/{name}-current-emission.json'
        meta = read_json(p)
        module = L / f'Port3_Native{name.title()}Body.lean'
        assert pin(module)['sha256'] == meta['module_sha256']
        emitted = R / 'evidence/ports3-20261023/current-children/Funs.lean'
        expected = meta.get('source_sha256', meta.get('generated_funs_sha256'))
        assert pin(emitted)['sha256'] == expected
        emissions.append({'metadata_pin': pin(p), 'retained_metadata': meta,
                          'emission_pin': pin(emitted), 'module_pin': pin(module)})

    # Full definitions/structures/statements, including proofs, are kept here
    # for review. They are snapshots of unchanged ROOT source, not new modules.
    names = '''VTop_Trace VTop_OracleCode Port15DRIVER_Local Port16CUT_Cuts
Port16CUT_Driver Port9OR_Installed Port9OR_Bodies Port3_Parents
Port3_QueryStage Port3_QueryInstall Port3_NativeQueryBody Port3_NativeRowFrame
Port4C_RowStd Port4C_QueryStd Port5Q1_QueryPorts Port5Q1_Complete
Port3_NativeFlushBody Port4D_FlushABI Port4D_Value Port4D_FlushRows
Port3_NativePendingBody Port3_NativePendingInstall Port3_Constructor Port3_Initial
Port3_GeometryStage Port3_NativeGeometryBody Port4C_Installed
Port5Q1_GeometryTerminal Port4C_GeometryInverse Port4C_CollectStd
Port3_NativeFinishBody Stage2FinishBody Port3_FinishStage Port4D_Round
Port4D_FinishInstall OraclePortStdAllocation OraclePortJoinSplitStd
CheckpointBytes3Allocation CheckpointBytes5Effect'''.split()
    roots = [L / (n + '.lean') for n in names]
    snapshots = []
    seen, unresolved = {}, set()
    def visit(p):
        if str(p) in seen:
            return
        text = p.read_text()
        assert p.read_bytes() == git('show', f'{base}:{p.relative_to(R)}')
        imports = re.findall(r'^import\s+(\S+)', text, re.M)
        seen[str(p)] = {**pin(p), 'imports': imports}
        for dep in imports:
            q = L / (dep.replace('.', '/') + '.lean')
            if q.exists():
                visit(q)
            else:
                unresolved.add(dep)
    for p in roots:
        visit(p)
        snapshots.append({**pin(p), 'complete_source': p.read_text()})

    # Reuse only the component receipt which actually pins this source hash.
    # Copy complete receipts: commands, dependency/object/tool pins, full axiom
    # reports and historical metrics. Do not inspect/revalidate host objects.
    receipts = []
    candidates = []
    for directory in ['ports3-20261023', 'port4c-20261023', 'port4d-20261023',
                      'port5q1-20261024', 'port16cut-20261024']:
        candidates += sorted((R / 'evidence' / directory).glob('lean-*/receipt.json'))
    for p in roots:
        matches = []
        for q in candidates:
            receipt = read_json(q)
            if (receipt.get('exit_status') == 0 and
                receipt.get('source_hashes', {}).get(p.name) == pin(p)['sha256']):
                matches.append((q, receipt))
        if matches:
            q, receipt = matches[-1]
            assert not any(bad in '\n'.join(receipt.get('print_axioms', []))
                           for bad in ['sorryAx', 'Lean.ofReduceBool', 'Lean.trustCompiler'])
            receipts.append({'module': p.stem, 'receipt_pin': pin(q),
                             'complete_historical_receipt': receipt,
                             'assessment': 'unchanged local source only; imported object '
                             'compatibility/native effects/artifact identity not revalidated'})
        else:
            receipts.append({'module': p.stem, 'assessment':
                             'no matching receipt in selected component directories; no proof credit'})

    cuts = (L / 'Port16CUT_Cuts.lean').read_text()
    expr = re.search(r'def delegatedWeight.*?:=\s*([^\n]+)', cuts).group(1)
    coefficients = {}
    for term in expr.split('+'):
        match = re.fullmatch(r'\s*(?:(\d+)\*)?w (\d+)\s*', term)
        assert match, term
        coefficients[int(match[2])] = int(match[1] or 1)
    selected = {i: coefficients[i] for i in sorted(IDS)}
    other = {i: n for i, n in coefficients.items() if i not in IDS | {7}}
    assert selected == {6: 2, 9: 2, 10: 2, 11: 2, 12: 1, 19: 1}
    assert other == {3: 2, 4: 1, 17: 1}
    out = {'schema': 'port19rest-source-preflight-v1', 'base_revision': base,
           'inspection_revision': git('rev-parse', 'HEAD').decode().strip(),
           'script_pin': pin(Path(__file__)), 'source_body_inventory_pin': pin(inventory),
           'constructor_reuse': {'metadata_pin': pin(constructor_meta_path),
                                'emission_pin': pin(constructor_emission),
                                'assessment': 'retained normalization evidence only; no native effect join'},
           'rows': rows, 'emissions': emissions, 'complete_interfaces': snapshots,
           'root_source_import_closure': sorted(seen.values(), key=lambda x: x['path']),
           'imports_outside_flat_root_source_directory': sorted(unresolved),
           'closure_assessment': 'source hash inventory only, NOT compiled dependency closure; '
           'no A sources read; Port18 coherence work not duplicated',
           'reused_component_receipts': receipts,
           'residual_coefficients': {'assigned_rows': selected, 'retained_A_rows': other,
                                     'prepare7': coefficients[7]},
           'new_attempts': {'Lean': 0, 'Rust': 0, 'Kani': 0, 'backend': 0, 'extraction': 0},
           'new_formal_results': [], 'native_obligations_removed': [],
           'new_or_changed_assumptions': [], 'status': 'blocked before compilation'}
    data = json.dumps(out, indent=2) + '\n'
    assert len(data.encode()) <= 5_000_000
    (E / 'inventory.json').write_text(data)
    (E / 'source-check.json').write_text(json.dumps({
        'kind': 'source-only inspection, not a formal result',
        'command': ['python3', 'tools/port19rest-20261024/Port19REST_inventory.py'],
        'exit_status': 0, 'wall_seconds': time.monotonic() - started,
        'self_peak_rss_bytes_macos': resource.getrusage(resource.RUSAGE_SELF).ru_maxrss,
        'child_metrics': 'not sampled; only Git read subprocesses, no compiler',
        'swap': 'not measured for source-only inspection',
        'source_revision': git('rev-parse', 'HEAD').decode().strip(),
        'script_pin': pin(Path(__file__)), 'inventory_pin': pin(E / 'inventory.json'),
        'formal_attempt_charge': 0, 'new_axioms_reports': []}, indent=2) + '\n')
    print(f'PASS source-only: {len(rows)} pinned Rust parents, {len(emissions)} retained emissions, '
          f'{len(snapshots)} complete interfaces, {len(seen)} ROOT source files; no native closure')

if __name__ == '__main__':
    main()
