#!/usr/bin/env python3
"""Format index-only triangular zero certificates; no field arithmetic."""
import argparse
import hashlib
import json
from pathlib import Path

ROOT = Path(__file__).resolve().parents[1]
CHUNK = 8

def chunks():
    paths = [ROOT/'evidence'/name for name in (
        'r17-minor-blocks.jsonl', 'r17-active-source-rows.json', 'r17-active-minor-columns.txt')]
    raw = [p.read_bytes() for p in paths]
    blocks = sorted([json.loads(s) for s in raw[0].splitlines()], key=lambda b: -b['order'])
    rows = json.loads(raw[1])['coefficient_indices']
    columns = json.loads(raw[2])
    assert sorted(r for b in blocks for r in b['rows']) == list(range(214))
    assert sorted(c for b in blocks for c in b['columns']) == list(range(214))
    leaves, pairs = [], 0
    for pos, block in enumerate(blocks):
        forbidden = [rows[r] for b in blocks[pos+1:] for r in b['rows']]
        for cc in block['columns']:
            col = columns[cc]
            base = 4*(22+col//3)
            q = base+1+col%3
            parity = 'odd' if q%2 else 'even'
            pairs += len(forbidden)
            name = f'column{cc}'
            leaves.append('\n'.join([
                f'def {name}_later : List ℕ := {forbidden}',
                f'theorem {name}_excluded : ∀ r ∈ {name}_later,',
                f'    ¬{parity}UnitSupport {q//2} r ∧ ¬evenUnitSupport {base//2} r := by decide',
                f'theorem {name}_zero {{F : Type*}} [CommRing F] (half t a b c : F)',
                f'    (r : ℕ) (hr : r ∈ {name}_later) :',
                f'    sourceChord half (fun i => unitVector {q} i-t*unitVector {base} i) a b c r = 0 := by',
                f'  obtain ⟨hq,hb⟩ := {name}_excluded r hr',
                '  rw [sourceChord_difference]',
                f'  rw [sourceChord_{parity}_zero half {q//2} r (by decide) hq,',
                f'      sourceChord_even_zero half {base//2} r (by decide) hb]',
                '  simp', f'#print axioms {name}_excluded', f'#print axioms {name}_zero', '']))
    assert len(leaves) == 214 and pairs == 22702
    header = '\n'.join(['import AspisV8R17.WeightedScatter', '',
        '/-! Generated arbitrary-field source-model zeros. Stable descending block order.',
        *[f'{p.name}: {hashlib.sha256(data).hexdigest()}' for p,data in zip(paths,raw)],
        'Index exclusions only; no evaluated field values or native_decide. -/',
        'set_option autoImplicit false', 'set_option maxRecDepth 2048',
        'namespace AspisV8R17.SourceBlockSupport', ''])
    return [header+'\n'.join(leaves[i:i+CHUNK])+'\nend AspisV8R17.SourceBlockSupport\n'
            for i in range(0,len(leaves),CHUNK)]

def main():
    p = argparse.ArgumentParser()
    p.add_argument('--chunk',type=int)
    p.add_argument('--check',action='store_true')
    args = p.parse_args()
    outputs = chunks()
    if args.check:
        for i, expected in enumerate(outputs):
            target = ROOT/f'lean/AspisV8R17/SourceBlockSupport{i:02}.lean'
            assert target.read_text() == expected, f'stale {target}'
        print(f'R17_BLOCK_SUPPORT_CHECK chunks={len(outputs)} columns=214 pairs=22702 match=true')
    else:
        assert args.chunk is not None and 0 <= args.chunk < len(outputs)
        print(outputs[args.chunk],end='')

if __name__ == '__main__':
    main()
