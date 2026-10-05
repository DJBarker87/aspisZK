#!/usr/bin/env python3
"""Generate per-row diagonal bindings and small aggregate block equalities."""
import argparse
import hashlib
import json
import re
import sys
from pathlib import Path

HERE = Path(__file__).resolve().parent
ROOT = Path('/Users/dominic/ZK/.worktrees/ZK-v8-r21-public-arithmetic-20260922')
sys.path.insert(0, str(HERE))
import generate as base

OUT = HERE / 'split-generated'
GREEN_ROW00 = HERE / 'rows/R807SourceBlock03Row00.lean'
GREEN_ROW00_SHA = '7dbf881e7bbde035fd9443707fb961ce3043872903388d81ef442f815a9a7543'
GREEN_BLOCK02_SHA = 'bfae56c59c03fb4cc770ac9f6a7612560c4e3bd4'

def row_modules():
    status = json.loads(base.STATUS.read_text())
    modules = {}
    hashes = {}
    for entry in status['green']:
        mod = entry['target'].split('/')[-1].removesuffix('.lean')
        for code in entry.get('rows', []):
            modules[code] = mod
            hashes[code] = entry['source_sha256']
    modules[114] = 'R804LiteralSourceRow114'
    hashes[114] = base.PINS['R804_row114']
    return modules, hashes

def render_rows(block, row_items, chunk):
    k = block['block']
    mod = f'R807SourceBlock{k:02d}RowsChunk{chunk:02d}'
    modules, _ = row_modules()
    needed = sorted(set(modules[code] for _, code, _ in row_items))
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
    ] + [f'AspisV8R19.{name}' for name in needed]
    lines = ['import ' + name for name in sorted(set(imports))]
    lines += [
        '', 'set_option autoImplicit false', 'set_option maxRecDepth 32768',
        'set_option maxHeartbeats 800000', f'namespace AspisV8R19.{mod}',
        'open AspisV8R19.R807SourceBlock01Binding',
        'open AspisV8R19.R804LiteralSourceRow114',
        'open AspisV8R19.R748JointWitnessPointEntry',
        'open AspisV8R19.R801LiteralActiveEntries',
        'open AspisV8R19.R799LiteralSourceMatrix',
        'open AspisV8R19.R806LiteralBlockLayout',
        'open AspisV8R19.R724BlockOrderMaps',
        'noncomputable section', '',
    ]
    for local, code, slot in row_items:
        rowmod = modules[code]
        lines += [
            f'theorem source_block{k:02d}_row{local:02d} :',
            f'    (fun j : Fin {block["size"]} => reorderedSourceMatrix (flatIndex {k} (⟨{local}, by decide⟩ : Fin {block["size"]})) (flatIndex {k} j)) =',
            f'      (fun j => R752SCC{k:02d}Matrix.A_scc (⟨{local}, by decide⟩ : Fin {block["size"]}) j) := by',
            '  funext j',
            '  change (literalSourceMatrix halfSelected quarterSelected alphaSelected uSelected vSelected',
            f'    kappaSelected tauSelected z) (activePosition (⟨{slot}, by decide⟩ : Fin 214))',
            f'    (colOrder (flatIndex {k} j)) = _',
            f'  rw [AspisV8R19.{rowmod}.literalSourceMatrix_row{code}]',
            '  fin_cases j <;> rfl',
            f'#print axioms source_block{k:02d}_row{local:02d}', '',
        ]
    lines += ['end', '', f'end AspisV8R19.{mod}', '']
    return '\n'.join(lines)

def render_aggregate(block, row_sources):
    k = block['block']
    n = block['size']
    mod = f'R807SourceBlock{k:02d}Binding'
    imports = [
        'AspisV8R19.R807SourceBlock01Binding',
        'AspisV8R19.R806LiteralBlockLayout',
        f'AspisV8R19.R813FiniteFunctionExt{n}',
        f'AspisV8R19.R752SCC{k:02d}Matrix',
    ] + [f'AspisV8R19.{name}' for name in sorted(set(v[0] for v in row_sources.values()))]
    lines = ['import ' + name for name in sorted(set(imports))]
    lines += [
        '', 'set_option autoImplicit false', 'set_option maxRecDepth 32768',
        'set_option maxHeartbeats 800000', f'namespace AspisV8R19.{mod}',
        'open AspisV8R19.R807SourceBlock01Binding',
        'open AspisV8R19.R806LiteralBlockLayout',
        'noncomputable section', '',
        f'theorem source_block{k:02d}_eq_certificate : diagonalSourceBlock {k} = R752SCC{k:02d}Matrix.A_scc := by',
        f'  apply AspisV8R19.R813FiniteFunctionExt{n}.fin{n}_ext',
    ]
    for local in range(block['size']):
        source = row_sources[local]
        rowmod, rowname = source
        lines += [f'  · exact AspisV8R19.{rowmod}.{rowname}']
    lines += [f'#print axioms source_block{k:02d}_eq_certificate', 'end', '', f'end AspisV8R19.{mod}', '']
    return '\n'.join(lines)

def main():
    p = argparse.ArgumentParser()
    g = p.add_mutually_exclusive_group(required=True)
    g.add_argument('--write', action='store_true')
    g.add_argument('--check', action='store_true')
    args = p.parse_args()
    blocks, _ = base.collect()
    modules, hashes = row_modules()
    if hashlib.sha256(GREEN_ROW00.read_bytes()).hexdigest() != GREEN_ROW00_SHA:
        raise SystemExit('green block03 row00 source changed')
    out_sources = {}
    block_records = []
    for b in blocks:
        k = b['block']
        if k == 2:
            continue  # already green as a whole-block theorem
        row_items = [(i, code, slot) for i, (code, slot) in enumerate(zip(b['row_codes'], b['active_slots']))]
        sources = {}
        if k == 3:
            sources[0] = ('R807SourceBlock03Row00', 'source_block03_row00')
            row_items = row_items[1:]
        # Keep source files bounded: one row at width 16, two rows at smaller widths.
        per_file = 1 if b['size'] >= 16 else 2
        groups = [row_items[i:i+per_file] for i in range(0, len(row_items), per_file)]
        for chunk, group in enumerate(groups):
            rowmod = f'R807SourceBlock{k:02d}RowsChunk{chunk:02d}'
            out_sources[OUT / f'{rowmod}.lean'] = render_rows(b, group, chunk)
            for local, _, _ in group:
                sources[local] = (rowmod, f'source_block{k:02d}_row{local:02d}')
        out_sources[OUT / f'R807SourceBlock{k:02d}Binding.lean'] = render_aggregate(b, sources)
        block_records.append({'block': k, 'size': b['size'], 'active_slots': b['active_slots'], 'row_codes': b['row_codes'], 'row_modules': sorted(set(v[0] for v in sources.values()))})
    expected = set(out_sources)
    existing = set(OUT.glob('R807SourceBlock*.lean')) if OUT.exists() else set()
    if args.check:
        if existing != expected:
            raise SystemExit(f'generated output set mismatch missing={len(expected-existing)} extra={len(existing-expected)}')
        for path, source in out_sources.items():
            if path.read_text() != source:
                raise SystemExit(f'generated source differs: {path}')
        print(f'check ok: {len(block_records)} split block aggregates, {len(out_sources)-len(block_records)} bounded row modules; block02 reused')
    else:
        OUT.mkdir(parents=True, exist_ok=True)
        for path, source in out_sources.items():
            path.write_text(source)
        print(f'wrote {len(block_records)} split block aggregates, {len(out_sources)-len(block_records)} bounded row modules; block02 reused')
    pins = dict(base.PINS)
    pins['green_block02_source_sha256'] = '7d5775184794e8aeedeb555c0c0436ce1f677a8e6272393277e9d918dc74dd0e'
    pins['green_block03_row00_source_sha256'] = GREEN_ROW00_SHA
    record = {'scope':'Fixed selected witness diagonal-block equality only. No determinant, rank, privacy, or soundness consequence.', 'pins':pins, 'blocks':block_records}
    (HERE / 'split-plan.json').write_text(json.dumps(record, indent=2)+'\n')

if __name__ == '__main__':
    main()
