#!/usr/bin/env python3
"""Emit checked permutations for the frozen minor's triangular block order."""
import argparse
import hashlib
import json
from pathlib import Path

ROOT = Path(__file__).resolve().parents[1]

def render():
    raw = (ROOT/'evidence/r17-minor-blocks.jsonl').read_bytes()
    blocks = sorted([json.loads(s) for s in raw.splitlines()], key=lambda b: -b['order'])
    lines = ['import Mathlib.Data.Fintype.Pi', 'import Mathlib.Data.List.GetD',
        '', '/-! Frozen row and column permutations, with kernel-checked inverses.',
        f'Block artifact SHA256: {hashlib.sha256(raw).hexdigest()}',
        'Stable descending order agrees with r17_block_support.py. -/',
        'set_option autoImplicit false', 'set_option maxRecDepth 2048',
        'namespace AspisV8R17.BlockOrdering', '',
        'def indexMap (xs : List ℕ) (i : Fin 214) : Fin 214 :=',
        '  ⟨xs.getD i.val 0 % 214, Nat.mod_lt _ (by decide)⟩', '']
    for name, field in [('row', 'rows'), ('column', 'columns')]:
        order = [i for b in blocks for i in b[field]]
        assert sorted(order) == list(range(214))
        inverse = [order.index(i) for i in range(214)]
        lines += [f'def {name}Order : List ℕ := {order}',
            f'def {name}Inverse : List ℕ := {inverse}',
            f'theorem {name}_left : ∀ i : Fin 214,',
            f'    indexMap {name}Inverse (indexMap {name}Order i) = i := by decide',
            f'theorem {name}_right : ∀ i : Fin 214,',
            f'    indexMap {name}Order (indexMap {name}Inverse i) = i := by decide',
            f'def {name}Perm : Equiv.Perm (Fin 214) where',
            f'  toFun := indexMap {name}Order', f'  invFun := indexMap {name}Inverse',
            f'  left_inv := {name}_left', f'  right_inv := {name}_right',
            f'#print axioms {name}_left', f'#print axioms {name}_right', '']
    lines += ['end AspisV8R17.BlockOrdering', '']
    return '\n'.join(lines)

def main():
    p = argparse.ArgumentParser()
    p.add_argument('--check', action='store_true')
    args = p.parse_args()
    result = render()
    if args.check:
        assert (ROOT/'lean/AspisV8R17/BlockOrdering.lean').read_text() == result
        print('R17_BLOCK_ORDERING_CHECK rows=214 columns=214 inverse_checks=4 match=true')
    else:
        print(result, end='')

if __name__ == '__main__':
    main()
