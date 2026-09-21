#!/usr/bin/env python3
"""Emit symbolic tail recursion, never expand a large determinant."""
import argparse
import hashlib
import json
from pathlib import Path

ROOT=Path(__file__).resolve().parents[1]

def render():
    raw=(ROOT/'evidence/r17-minor-blocks.jsonl').read_bytes()
    blocks=sorted([json.loads(s) for s in raw.splitlines()],key=lambda b:-b['order'])
    offsets=[0]
    for b in blocks: offsets.append(offsets[-1]+len(b['rows']))
    assert len(blocks)==133 and offsets[-1]==214
    out=[*[f'import AspisV8R17.SourceWindowBlocks{i:02}' for i in range(17)],'',
         '/-! Generated symbolic source-minor determinant composition.',
         'Frozen block SHA256: '+hashlib.sha256(raw).hexdigest(),
         'Fixed algebraic witness only; not a source sampler or global privacy theorem. -/',
         'set_option autoImplicit false',
         'namespace AspisV8R17.SourceMinor.Windows','',
         'theorem tail133_unit : IsUnit (matrixWindow sourceMatrix 214 0).det := by',
         '  rw [Matrix.det_isEmpty]', '  exact isUnit_one', '#print axioms tail133_unit','']
    for k in reversed(range(133)):
        start,end=offsets[k:k+2];size=end-start
        out += [f'theorem tail{k}_unit : IsUnit (matrixWindow sourceMatrix {start} {214-start}).det := by',
                f'  exact matrixWindow_isUnit sourceMatrix {start} {size} {214-end}',
                f'    block{k}_lower block{k}_unit tail{k+1}_unit',f'#print axioms tail{k}_unit','']
    out += ['theorem ordered_minor_det_isUnit :',
            '    IsUnit (Matrix.det (orderedMinor (1073741824 : ZMod 2147483647) 2 13 11 (-7))) := by',
            '  have h := tail0_unit', '  rw [full_window_eq] at h', '  exact h','',
            'theorem source_minor_det_ne_zero :',
            '    Matrix.det (minor (1073741824 : ZMod 2147483647) 2 13 11 (-7)) ≠ 0 := by',
            '  letI : Fact (1 < (2147483647 : ℕ)) := ⟨by decide⟩',
            '  have h := ordered_minor_det_isUnit.ne_zero',
            '  change Matrix.det (Matrix.reindex BlockOrdering.rowPerm.symm BlockOrdering.columnPerm.symm',
            '    (minor (1073741824 : ZMod 2147483647) 2 13 11 (-7))) ≠ 0 at h',
            '  rw [Matrix.det_reindex] at h', '  intro hz', '  exact h (by rw [hz, mul_zero])','',
            '#print axioms ordered_minor_det_isUnit','#print axioms source_minor_det_ne_zero',
            'end AspisV8R17.SourceMinor.Windows','']
    return '\n'.join(out)

def main():
    p=argparse.ArgumentParser();p.add_argument('--check',action='store_true');args=p.parse_args()
    s=render()
    if args.check:
        assert (ROOT/'lean/AspisV8R17/SourceMinorDeterminant.lean').read_text()==s
        print('R17_SOURCE_DETERMINANT_CHECK blocks=133 tails=134 match=true')
    else: print(s,end='')

if __name__=='__main__': main()
