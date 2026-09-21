#!/usr/bin/env python3
"""Bind checked zero certificates to every lower block of the source minor."""
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
    columns = json.loads(raw[2])
    leaves, offset, pairs = [], 0, 0
    for block in blocks:
        size = len(block['columns'])
        end = offset+size
        for j, cc in enumerate(block['columns']):
            col = columns[cc]
            base, channel = 4*(22+col//3), 1+col%3
            name = f'column{cc}'
            leaves.append('\n'.join([
                f'theorem {name}_tail : orderedRows.drop {end} = SourceBlockSupport.{name}_later := by decide',
                f'theorem {name}_lower {{F : Type*}} [CommRing F] (half alpha a b c : F)',
                f'    (i : Fin {214-end}) :',
                f'    orderedMinor half alpha a b c ⟨{end}+i.val, by omega⟩ {offset+j} = 0 := by',
                '  rw [orderedMinor_entry]',
                f'  change entry half alpha a b c (orderedRows.getD ({end}+i.val) 0) {col} = 0',
                '  unfold entry',
                f'  simp only [show 4*(22+{col}/3) = {base} from rfl,',
                f'    show 1+{col}%3 = {channel} from rfl, show {base}+{channel} = {base+channel} from rfl]',
                f'  exact SourceBlockSupport.{name}_zero half (alpha^{channel}) a b c _',
                f'    (tail_lookup_mem orderedRows _ {end} {214-end} {name}_tail (by decide) i)',
                f'#print axioms {name}_tail', f'#print axioms {name}_lower', '']))
            pairs += 214-end
        offset = end
    assert offset == len(leaves) == 214 and pairs == 22702
    out = []
    for i in range(0, len(leaves), CHUNK):
        header = '\n'.join(['import AspisV8R17.TailLookup',
            f'import AspisV8R17.SourceBlockSupport{i//CHUNK:02}', '',
            '/-! Generated source-matrix lower-block bindings. Inputs:',
            *[f'{p.name}: {hashlib.sha256(data).hexdigest()}' for p,data in zip(paths,raw)],
            'Uses symbolic tail membership, no repeated full lookup decisions. -/',
            'set_option autoImplicit false', 'set_option maxRecDepth 2048',
            'namespace AspisV8R17.SourceMinor.LowerBlocks', ''])
        out.append(header+'\n'.join(leaves[i:i+CHUNK])+'\nend AspisV8R17.SourceMinor.LowerBlocks\n')
    return out

def main():
    p = argparse.ArgumentParser()
    p.add_argument('--chunk', type=int)
    p.add_argument('--check', action='store_true')
    args = p.parse_args()
    out = chunks()
    if args.check:
        for i, result in enumerate(out):
            assert (ROOT/f'lean/AspisV8R17/SourceLowerBlocks{i:02}.lean').read_text() == result
        print('R17_SOURCE_LOWER_CHECK chunks=27 columns=214 pairs=22702 match=true')
    else:
        assert args.chunk is not None and 0 <= args.chunk < len(out)
        print(out[args.chunk], end='')

if __name__ == '__main__':
    main()
