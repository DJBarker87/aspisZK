#!/usr/bin/env python3
"""Format source-model block equality chunks; no field arithmetic search."""
import argparse
import hashlib
import json
from pathlib import Path

ROOT = Path(__file__).resolve().parents[1]
CHUNK = 32

def chunks():
    paths = [ROOT/'evidence'/name for name in (
        'r17-minor-blocks.jsonl', 'r17-active-source-rows.json', 'r17-active-minor-columns.txt')]
    raw = [p.read_bytes() for p in paths]
    blocks = [json.loads(s) for s in raw[0].splitlines()]
    rows = json.loads(raw[1])['coefficient_indices']
    columns = json.loads(raw[2])
    assert len(blocks) == 133 and len(rows) == len(columns) == 214
    leaves = []
    for b, block in enumerate(blocks):
        size = len(block['rows'])
        assert size in (1,2,3) and len(block['values']) == size*size
        for i, rr in enumerate(block['rows']):
            for j, cc in enumerate(block['columns']):
                col = columns[cc]
                degree, channel = 22+col//3, 1+col%3
                q, base, r = 4*degree+channel, 4*degree, rows[rr]
                value = block['values'][i*size+j]
                assert q//2 < 512 and base//2 < 512
                parity = 'odd' if q%2 else 'even'
                name = f'block{b}_entry{i}_{j}'
                leaves.append('\n'.join([
                    f'theorem {name} :',
                    '    sourceChord (1073741824 : ZMod 2147483647)',
                    f'      (fun i => unitVector {q} i-{2**channel}*unitVector {base} i)',
                    f'      13 11 (-7) {r} = {value} := by',
                    '  rw [sourceChord_difference]',
                    f'  rw [sourceChord_unit_{parity} _ {q//2} {r} (by decide),',
                    f'      sourceChord_unit_even _ {base//2} {r} (by decide)]',
                    '  decide', f'#print axioms {name}', '']))
    assert len(leaves) == 392
    header = '\n'.join(['import AspisV8R17.WeightedScatter', 'import Mathlib.Data.ZMod.Basic', '',
        '/-! Generated sparse source-model block entries. Inputs:',
        *[f'{p.name}: {hashlib.sha256(data).hexdigest()}' for p,data in zip(paths,raw)],
        'Uses named sparse rewrites; never unfolds the full source edge list. -/',
        'set_option autoImplicit false', 'namespace AspisV8R17.SourceBlocks', ''])
    return [header+'\n'.join(leaves[i:i+CHUNK])+'\nend AspisV8R17.SourceBlocks\n'
            for i in range(0,len(leaves),CHUNK)]

def main():
    p = argparse.ArgumentParser()
    p.add_argument('--chunk',type=int)
    p.add_argument('--check',action='store_true')
    args = p.parse_args()
    outputs = chunks()
    if args.check:
        for i, expected in enumerate(outputs):
            target = ROOT/f'lean/AspisV8R17/SourceBlockEntries{i:02}.lean'
            assert target.read_text() == expected, f'stale {target}'
        print(f'R17_SOURCE_BLOCK_CHECK chunks={len(outputs)} entries=392 match=true')
    else:
        assert args.chunk is not None and 0 <= args.chunk < len(outputs)
        print(outputs[args.chunk],end='')

if __name__ == '__main__':
    main()
