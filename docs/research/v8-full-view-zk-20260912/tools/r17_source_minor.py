#!/usr/bin/env python3
"""Emit the frozen source-model minor and checked ordered index projections."""
import argparse
import hashlib
import json
from pathlib import Path

ROOT = Path(__file__).resolve().parents[1]

def render():
    paths = [ROOT/'evidence'/name for name in (
        'r17-minor-blocks.jsonl', 'r17-active-source-rows.json', 'r17-active-minor-columns.txt')]
    raw = [p.read_bytes() for p in paths]
    blocks = sorted([json.loads(s) for s in raw[0].splitlines()], key=lambda b: -b['order'])
    rows = json.loads(raw[1])['coefficient_indices']
    cols = json.loads(raw[2])
    ordered_rows = [rows[i] for b in blocks for i in b['rows']]
    ordered_cols = [cols[i] for b in blocks for i in b['columns']]
    assert len(rows) == len(cols) == len(ordered_rows) == len(ordered_cols) == 214
    lines = ['import AspisV8R17.WeightedScatter', 'import AspisV8R17.BlockOrdering', '',
        '/-! Source-shaped minor. Artifact correspondence is explicit, not an extraction theorem.',
        *[f'{p.name}: {hashlib.sha256(data).hexdigest()}' for p,data in zip(paths,raw)],
        '-/', 'set_option autoImplicit false', 'set_option maxRecDepth 2048',
        'namespace AspisV8R17.SourceMinor', '',
        f'def sourceRows : List ℕ := {rows}', f'def selectedColumns : List ℕ := {cols}',
        f'def orderedRows : List ℕ := {ordered_rows}', f'def orderedColumns : List ℕ := {ordered_cols}', '',
        'theorem projected_lookup (xs ys zs : List ℕ)',
        '    (h : zs = xs.map (fun j => ys.getD (j%214) 0))',
        '    (hlen : xs.length = 214) (i : Fin 214) :',
        '    ys.getD (BlockOrdering.indexMap xs i).val 0 = zs.getD i.val 0 := by',
        '  have hi : i.val < xs.length := by rw [hlen]; exact i.isLt',
        '  rw [h, List.getD_eq_getElem (xs.map (fun j => ys.getD (j%214) 0)) 0',
        '    (by simpa only [List.length_map] using hi)]',
        '  change ys.getD (xs.getD i.val 0 % 214) 0 = _',
        '  rw [List.getD_eq_getElem xs 0 hi]',
        '  rw [List.getElem_map]', '',
        'theorem row_map : orderedRows = BlockOrdering.rowOrder.map',
        '    (fun j => sourceRows.getD (j%214) 0) := by decide',
        'theorem column_map : orderedColumns = BlockOrdering.columnOrder.map',
        '    (fun j => selectedColumns.getD (j%214) 0) := by decide',
        'theorem row_projection (i : Fin 214) :',
        '    sourceRows.getD (BlockOrdering.rowPerm i).val 0 = orderedRows.getD i.val 0 :=',
        '  projected_lookup _ _ _ row_map (by decide) i',
        'theorem column_projection (i : Fin 214) :',
        '    selectedColumns.getD (BlockOrdering.columnPerm i).val 0 = orderedColumns.getD i.val 0 :=',
        '  projected_lookup _ _ _ column_map (by decide) i', '',
        'variable {F : Type*} [CommRing F]',
        'def entry (half alpha a b c : F) (r col : ℕ) : F :=',
        '  let base := 4*(22+col/3)', '  let channel := 1+col%3',
        '  sourceChord half (fun i => unitVector (base+channel) i-alpha^channel*unitVector base i) a b c r', '',
        'def minor (half alpha a b c : F) (i j : Fin 214) : F :=',
        '  entry half alpha a b c (sourceRows.getD i.val 0) (selectedColumns.getD j.val 0)', '',
        'def orderedMinor (half alpha a b c : F) (i j : Fin 214) : F :=',
        '  minor half alpha a b c (BlockOrdering.rowPerm i) (BlockOrdering.columnPerm j)', '',
        'theorem orderedMinor_entry (half alpha a b c : F) (i j : Fin 214) :',
        '    orderedMinor half alpha a b c i j =',
        '      entry half alpha a b c (orderedRows.getD i.val 0) (orderedColumns.getD j.val 0) := by',
        '  unfold orderedMinor minor', '  rw [row_projection, column_projection]', '',
        '#print axioms row_projection', '#print axioms column_projection',
        '#print axioms orderedMinor_entry', 'end AspisV8R17.SourceMinor', '']
    return '\n'.join(lines)

def main():
    p = argparse.ArgumentParser()
    p.add_argument('--check', action='store_true')
    args = p.parse_args()
    result = render()
    if args.check:
        assert (ROOT/'lean/AspisV8R17/SourceMinor.lean').read_text() == result
        print('R17_SOURCE_MINOR_CHECK rows=214 columns=214 projections=2 match=true')
    else:
        print(result, end='')

if __name__ == '__main__':
    main()
