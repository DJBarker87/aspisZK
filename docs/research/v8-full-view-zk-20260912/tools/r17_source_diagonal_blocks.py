#!/usr/bin/env python3
"""Bind frozen diagonal values to coordinates of the ordered source minor."""
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
    cols = json.loads(raw[2])
    offsets, offset = {}, 0
    for b in sorted(range(len(blocks)), key=lambda b: -blocks[b]['order']):
        offsets[b] = offset
        offset += len(blocks[b]['rows'])
    assert offset == 214
    leaves = []
    for b, block in enumerate(blocks):
        size = len(block['rows'])
        for i, rr in enumerate(block['rows']):
            for j, cc in enumerate(block['columns']):
                col, r = cols[cc], rows[rr]
                base, channel = 4*(22+col//3), 1+col%3
                value = block['values'][i*size+j]
                name = f'block{b}_entry{i}_{j}'
                leaves.append('\n'.join([
                    f'theorem {name} :',
                    '    orderedMinor (1073741824 : ZMod 2147483647) 2 13 11 (-7)',
                    f'      {offsets[b]+i} {offsets[b]+j} = {value} := by',
                    '  rw [orderedMinor_entry]',
                    f'  change entry (1073741824 : ZMod 2147483647) 2 13 11 (-7) {r} {col} = {value}',
                    '  unfold entry',
                    f'  simp only [show 4*(22+{col}/3) = {base} from rfl,',
                    f'    show 1+{col}%3 = {channel} from rfl, show {base}+{channel} = {base+channel} from rfl]',
                    f'  rw [show (2 : ZMod 2147483647)^{channel} = {2**channel} from by decide]',
                    f'  exact SourceBlocks.{name}', f'#print axioms {name}', '']))
    assert len(leaves) == 392
    out = []
    for i in range(0,len(leaves),CHUNK):
        header = '\n'.join(['import AspisV8R17.SourceMinor',
            f'import AspisV8R17.SourceBlockEntries{i//CHUNK:02}', '',
            '/-! Generated source-matrix diagonal bindings. Inputs:',
            *[f'{p.name}: {hashlib.sha256(data).hexdigest()}' for p,data in zip(paths,raw)],
            'Preserve entry head before rewriting indices; never unfold full scatter. -/',
            'set_option autoImplicit false', 'set_option maxRecDepth 2048',
            'namespace AspisV8R17.SourceMinor.DiagonalBlocks', ''])
        out.append(header+'\n'.join(leaves[i:i+CHUNK])+'\nend AspisV8R17.SourceMinor.DiagonalBlocks\n')
    return out

def main():
    p = argparse.ArgumentParser()
    p.add_argument('--chunk',type=int)
    p.add_argument('--check',action='store_true')
    args = p.parse_args()
    out = chunks()
    if args.check:
        for i,result in enumerate(out):
            assert (ROOT/f'lean/AspisV8R17/SourceDiagonalBlocks{i:02}.lean').read_text() == result
        print('R17_SOURCE_DIAGONAL_CHECK chunks=13 entries=392 match=true')
    else:
        assert args.chunk is not None and 0 <= args.chunk < len(out)
        print(out[args.chunk],end='')

if __name__ == '__main__':
    main()
