#!/usr/bin/env python3
"""Generate fixed-source diagonal equality modules for active-only SCC blocks."""
import argparse
import hashlib
import json
import re
from pathlib import Path

ROOT = Path('/Users/dominic/ZK/.worktrees/ZK-v8-r21-public-arithmetic-20260922')
SCRATCH = ROOT / '.r21-scratch/r807-active-diagonal'
STATUS = ROOT / '.r21-scratch/r804-literal-row-generator/R804_STATUS.json'
SUPPORT = ROOT / 'docs/research/v8-full-view-zk-20260912/evidence/r787-complete-active-nonzero-cells/inputs/support-check.json'
LAYOUT = ROOT / 'docs/research/v8-full-view-zk-20260912/lean/AspisV8R19/R806LiteralBlockLayout.lean'
ORDER = ROOT / 'docs/research/v8-full-view-zk-20260912/lean/AspisV8R19/R724BlockOrderMaps.lean'
R799 = ROOT / 'docs/research/v8-full-view-zk-20260912/lean/AspisV8R19/R799LiteralSourceMatrix.lean'
R766 = ROOT / 'docs/research/v8-full-view-zk-20260912/lean/AspisV8R19/R766BlockOrderEquivalences.lean'
R807 = ROOT / '.r21-scratch/R807SourceBlock01Binding.lean'
R804_114 = ROOT / 'docs/research/v8-full-view-zk-20260912/lean/AspisV8R19/R804LiteralSourceRow114.lean'
OUT = SCRATCH / 'generated'
PINS = {
    'R804_STATUS': '58e0ff2b1581e7eb108e617d775e2d2a368b2ff69a55774da11a216f32032d05',
    'support_check': '4ddaff34fc112bc64cb5484b81c7af7e96f10301326ce3a686b39ca4f641b592',
    'R806': '57f6facc9eba7dbc97ab53dd069859e7e5c8bbbaaf0af40a5ca5a04de392ebdf',
    'R724': '678b4a2a53ad1fa75f0c6bdb78f57c7eb385e5b71f18dc1f0dca451f155280e1',
    'R799': '96400bc6b233283fd93997d11176808f8114f8366498ca76880a9206f4363e3a',
    'R766': '042115f7b61271fc88f1285d162638f674efaa1b7295b2ebac638db0988e86f4',
    'R807_prototype': '8806645f12e582eea93bbf4d6a42bcadcee15ed205c129a466c67f6adc78f25a',
    'R804_row114': 'd4d70f5fc4794f00ba2e6e7020153e52353ff3c29b626dda2d44898a470648e2',
}

def sha(path):
    return hashlib.sha256(path.read_bytes()).hexdigest()

def literal_cases(text, name, default):
    segment = text.split(f'def {name} ', 1)[1].split('\ndef ', 1)[0]
    result = {int(i): int(v) for i, v in re.findall(r'\|\s*(\d+)\s*=>\s*(\d+)', segment)}
    result[40] = default
    return result

def collect():
    inputs = {
        'R804_STATUS': STATUS, 'support_check': SUPPORT, 'R806': LAYOUT,
        'R724': ORDER, 'R799': R799, 'R766': R766,
        'R807_prototype': R807, 'R804_row114': R804_114,
    }
    for key, path in inputs.items():
        actual = sha(path)
        expected = PINS[key]
        if key == 'R807_prototype':
            # The prototype itself was audited by the lead; fail closed on any source change.
            if actual != expected:
                raise SystemExit(f'{key} SHA mismatch {actual} != {expected}')
        elif actual != expected:
            raise SystemExit(f'{key} SHA mismatch {actual} != {expected}')
    status = json.loads(STATUS.read_text())
    support = json.loads(SUPPORT.read_text())
    rowcode_by_slot = {row['row_slot']: row['row_code'] for row in support['rows']}
    if len(rowcode_by_slot) != 214:
        raise SystemExit('support-check row-slot count changed')
    row_module = {}
    row_sha = {}
    for record in status['green']:
        source = ROOT / record['source']
        if sha(source) != record['source_sha256']:
            raise SystemExit(f"R804 row source checksum mismatch: {source}")
        mod = record['target'].split('/')[-1].removesuffix('.lean')
        for code in record.get('rows', []):
            if code in row_module:
                raise SystemExit(f'duplicate R804 row theorem code {code}')
            row_module[code] = mod
            row_sha[code] = record['source_sha256']
    row_module[114] = 'R804LiteralSourceRow114'
    row_sha[114] = PINS['R804_row114']
    if set(row_module) != set(rowcode_by_slot.values()):
        raise SystemExit('R804 green row theorem coverage does not match 214 support rows')
    layout = LAYOUT.read_text()
    sizes = literal_cases(layout, 'blockSize', 1)
    offsets = literal_cases(layout, 'blockOffset', 221)
    if len(sizes) != 41 or len(offsets) != 41:
        raise SystemExit('block size/offset table is incomplete')
    order_text = ORDER.read_text().split('def rowOrder ', 1)[1].split('\ndef rowOrderInv', 1)[0]
    row_order = {int(i): int(v) for i, v in re.findall(r'\|\s*(\d+)\s*=>\s*(\d+)', order_text)}
    if len(row_order) != 222:
        raise SystemExit('rowOrder table is incomplete')
    blocks = []
    for k in range(41):
        if k in (0, 1, 6):
            continue
        off, size = offsets[k], sizes[k]
        active_slots = [row_order[off + j] for j in range(size)]
        if not all(slot in rowcode_by_slot for slot in active_slots):
            raise SystemExit(f'block {k} contains a non-active row')
        codes = [rowcode_by_slot[slot] for slot in active_slots]
        if not all(code in row_module for code in codes):
            raise SystemExit(f'block {k} refers to an unproved row theorem')
        blocks.append({
            'block': k, 'offset': off, 'size': size,
            'active_slots': active_slots, 'row_codes': codes,
            'row_modules': sorted(set(row_module[code] for code in codes)),
            'row_module_sha256': {row_module[code]: row_sha[code] for code in codes},
        })
    if len(blocks) != 38 or sum(block['size'] for block in blocks) != 176:
        raise SystemExit('active-only diagonal block coverage changed')
    return blocks, row_module

def render(block):
    k = block['block']
    module = f'R807SourceBlock{k:02d}Binding'
    imports = [
        'AspisV8R19.R807SourceBlock01Binding',
        'AspisV8R19.R806LiteralBlockLayout',
        'AspisV8R19.R724BlockOrderMaps',
        'AspisV8R19.R766BlockOrderEquivalences',
        'AspisV8R19.R748JointWitnessPointEntry',
        'AspisV8R19.R799LiteralSourceMatrix',
        'AspisV8R19.R801LiteralActiveEntries',
        f'AspisV8R19.R752SCC{k:02d}Matrix',
        'Mathlib.Tactic.FinCases',
    ]
    imports += [f"AspisV8R19.{name}" for name in block['row_modules']]
    lines = ['import ' + name for name in sorted(set(imports))]
    lines += [
        '', 'set_option autoImplicit false', 'set_option maxRecDepth 32768',
        'set_option maxHeartbeats 800000', f'namespace AspisV8R19.{module}',
        'open AspisV8R19.R807SourceBlock01Binding',
        'open AspisV8R19.R804LiteralSourceRow114',
        'open AspisV8R19.R748JointWitnessPointEntry',
        'open AspisV8R19.R801LiteralActiveEntries',
        'open AspisV8R19.R799LiteralSourceMatrix',
        'open AspisV8R19.R806LiteralBlockLayout',
        'open AspisV8R19.R724BlockOrderMaps',
        'noncomputable section', '',
        f'theorem source_block{k:02d}_eq_certificate : diagonalSourceBlock {k} = R752SCC{k:02d}Matrix.A_scc := by',
        '  ext i j', '  fin_cases i',
    ]
    for active, code in zip(block['active_slots'], block['row_codes']):
        rowmod = next(name for name in block['row_modules'] if code in row_code_set(name))
        lines += [
            '  · change (literalSourceMatrix halfSelected quarterSelected alphaSelected uSelected vSelected',
            f'      kappaSelected tauSelected z) (activePosition (⟨{active}, by decide⟩ : Fin 214))',
            f'      (colOrder (flatIndex {k} j)) = _',
            f'    rw [AspisV8R19.{rowmod}.literalSourceMatrix_row{code}]',
            '    fin_cases j <;> rfl',
        ]
    lines += [f'#print axioms source_block{k:02d}_eq_certificate', 'end', '', f'end AspisV8R19.{module}', '']
    return '\n'.join(lines)

_row_code_cache = None
def row_code_set(module):
    global _row_code_cache
    if _row_code_cache is None:
        status = json.loads(STATUS.read_text())
        _row_code_cache = {}
        for r in status['green']:
            mod = r['target'].split('/')[-1].removesuffix('.lean')
            for code in r.get('rows', []):
                _row_code_cache.setdefault(mod, set()).add(code)
        _row_code_cache['R804LiteralSourceRow114'] = {114}
    return _row_code_cache.get(module, set())

def main():
    parser = argparse.ArgumentParser()
    group = parser.add_mutually_exclusive_group(required=True)
    group.add_argument('--check', action='store_true')
    group.add_argument('--write', action='store_true')
    args = parser.parse_args()
    blocks, _ = collect()
    expected = {OUT / f"R807SourceBlock{b['block']:02d}Binding.lean": render(b) for b in blocks}
    existing = set(OUT.glob('R807SourceBlock*Binding.lean')) if OUT.exists() else set()
    if args.check:
        if existing != set(expected):
            raise SystemExit('generated output set mismatch')
        for path, source in expected.items():
            if path.read_text() != source:
                raise SystemExit(f'generated file differs: {path}')
        print('check ok: 38 active-only diagonal equality modules, 176 rows; blocks 00/06 excluded and 01 reused')
    else:
        OUT.mkdir(parents=True, exist_ok=True)
        for path, source in expected.items():
            path.write_text(source)
        print('wrote 38 active-only diagonal equality modules, 176 rows')
    plan = {
        'scope': 'Fixed selected witness and literal certificate diagonal-block equality only; no determinant/rank/privacy implication.',
        'pins': PINS,
        'blocks': blocks,
    }
    (SCRATCH / 'source-plan.json').write_text(json.dumps(plan, indent=2) + '\n')

if __name__ == '__main__':
    main()
