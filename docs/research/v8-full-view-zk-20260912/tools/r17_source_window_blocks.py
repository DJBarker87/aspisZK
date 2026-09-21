#!/usr/bin/env python3
"""Assemble finite source windows from named scalar certificates."""
import argparse
import hashlib
import json
from pathlib import Path

ROOT = Path(__file__).resolve().parents[1]
CHUNK = 8

def split(var, size, indent):
    pad = ' '*indent
    if size == 1:
        return [f'{pad}have h{var} : {var} = 0 := by omega', f'{pad}subst {var}']
    return [f'{pad}have h{var} : '+ ' ∨ '.join(f'{var} = {i}' for i in range(size))+' := by omega',
            f'{pad}rcases h{var} with '+' | '.join('rfl' for _ in range(size))]

def chunks():
    raw = (ROOT/'evidence/r17-minor-blocks.jsonl').read_bytes()
    blocks = [json.loads(s) for s in raw.splitlines()]
    sorted_ids = sorted(range(len(blocks)), key=lambda b: -blocks[b]['order'])
    unique, diag_chunks, entry_count = [], {}, 0
    for b, block in enumerate(blocks):
        key = tuple(block['values'])
        if key not in unique: unique.append(key)
        for i in range(len(block['rows'])):
            for j in range(len(block['columns'])):
                diag_chunks[b,i,j] = entry_count//32
                entry_count += 1
    leaves, offset = [], 0
    for pos,b in enumerate(sorted_ids):
        block = blocks[b]; size = len(block['rows']); end = offset+size
        case = unique.index(tuple(block['values']))
        imports = {f'AspisV8R17.SourceDiagonalBlocks{diag_chunks[b,i,j]:02}'
                   for i in range(size) for j in range(size)}
        imports |= {f'AspisV8R17.SourceLowerBlocks{(offset+j)//8:02}' for j in range(size)}
        lines = [f'theorem block{pos}_eq : matrixWindow sourceMatrix {offset} {size} = BlockDeterminants.block{case} := by',
                 '  ext i j'] + split('i',size,2)
        for i in range(size):
            if size>1: lines += ['  ·']
            indent = 4 if size>1 else 2
            lines += split('j',size,indent)
            for j in range(size):
                if size>1: lines += [' '*indent+'·']
                pad = ' '*(indent+2 if size>1 else indent)
                rr,cc = offset+i,offset+j
                lines += [f'{pad}change sourceMatrix {rr} {cc} = {block["values"][i*size+j]}',
                          f'{pad}rw [sourceMatrix_at _ _ (by decide) (by decide)]',
                          f'{pad}exact DiagonalBlocks.block{b}_entry{i}_{j}']
        lines += [f'theorem block{pos}_unit : IsUnit (matrixWindow sourceMatrix {offset} {size}).det := by',
                  f'  rw [block{pos}_eq]', f'  exact BlockDeterminants.block{case}_det_isUnit',
                  f'theorem block{pos}_lower : ∀ (i : Fin {214-end}) (j : Fin {size}),',
                  f'    sourceMatrix ({offset}+{size}+i.val) ({offset}+j.val) = 0 := by', '  intro i j']
        lines += split('j',size,2)
        for j,cc in enumerate(block['columns']):
            if size>1: lines += ['  ·']
            pad = ' '* (4 if size>1 else 2)
            lines += [f'{pad}change sourceMatrix ({end}+i.val) {offset+j} = 0',
                      f'{pad}rw [sourceMatrix_at _ _ (by omega) (by decide)]',
                      f'{pad}exact LowerBlocks.column{cc}_lower 1073741824 2 13 11 (-7) i']
        lines += [f'#print axioms block{pos}_eq', f'#print axioms block{pos}_unit', f'#print axioms block{pos}_lower','']
        leaves.append((imports,'\n'.join(lines)));offset=end
    assert offset==214 and len(leaves)==133
    out=[]
    for i in range(0,len(leaves),CHUNK):
        part=leaves[i:i+CHUNK]
        imports={'AspisV8R17.SourceMatrixWindow','AspisV8R17.BlockDeterminants'}
        imports.update(x for im,_ in part for x in im)
        header='\n'.join([*['import '+x for x in sorted(imports)],'',
            '/-! Generated concrete source-window bindings.',
            'Frozen block SHA256: '+hashlib.sha256(raw).hexdigest(),
            'Only finite cases of size at most three; named source entry and zero proofs. -/',
            'set_option autoImplicit false','set_option maxRecDepth 2048',
            'namespace AspisV8R17.SourceMinor.Windows',''])
        out.append(header+'\n'.join(s for _,s in part)+'\nend AspisV8R17.SourceMinor.Windows\n')
    return out

def main():
    p=argparse.ArgumentParser();p.add_argument('--chunk',type=int);p.add_argument('--check',action='store_true')
    args=p.parse_args();out=chunks()
    if args.check:
        for i,s in enumerate(out):
            assert (ROOT/f'lean/AspisV8R17/SourceWindowBlocks{i:02}.lean').read_text()==s
        print('R17_SOURCE_WINDOW_CHECK chunks=17 blocks=133 match=true')
    else:
        assert args.chunk is not None and 0<=args.chunk<len(out)
        print(out[args.chunk],end='')

if __name__=='__main__': main()
