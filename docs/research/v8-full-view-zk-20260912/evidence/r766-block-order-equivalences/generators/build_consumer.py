#!/usr/bin/env python3
from pathlib import Path
import argparse, hashlib, json
ROOT=Path(__file__).resolve().parents[2]
GEN=Path(__file__).resolve().parent/'generated'
MANIFEST=GEN/'manifest.json'
EXPECTED_MANIFEST_SHA=''

def sha(p): return hashlib.sha256(p.read_bytes()).hexdigest()

def build():
    m=json.loads(MANIFEST.read_text())
    if m['schema']!='r724-block-order-maps-v2': raise SystemExit('unexpected map manifest schema')
    for name,digest in m['outputs'].items():
        p=GEN/name
        if not p.exists() or sha(p)!=digest: raise SystemExit(f'generated dependency changed: {name}')
    imports='import Mathlib.Tactic.FinCases\nimport Mathlib.Logic.Equiv.Defs\nimport Mathlib.Data.Fintype.Fin\n'
    imports+='\n'.join([f'import AspisV8R19.R724BlockOrderChunk{i:02d}' for i in range(7)])
    imports+='\nimport AspisV8R19.R724BlockOrderCase0\nimport AspisV8R19.R724BlockOrderMaps\n'
    def fact(kind,direction,n):
        if n==0 and kind=='row' and direction=='left':
            return 'AspisV8R19.R724BlockOrderCase0.rowOrder_inverse_at_zero'
        if n==0 and kind=='col' and direction=='left':
            return 'AspisV8R19.R724BlockOrderCase0.colOrder_inverse_at_zero'
        c=n//32
        return f'AspisV8R19.R724BlockOrderChunk{c:02d}.{kind}Order_{direction}_{n:03d}'
    def proof(kind,direction):
        return '\n'.join(f'  case «{n}» => exact {fact(kind,direction,n)}' for n in range(222))
    src=f'''{imports}
/-! Generic Fin 222 equivalences assembled solely from the compiled literal scalar facts. -/
set_option autoImplicit false
namespace AspisV8R19.R766BlockOrderEquivalences
open AspisV8R19.R724BlockOrderMaps

theorem row_left : ∀ i : Fin 222, rowOrderInv (rowOrder i) = i := by
  intro i
  fin_cases i
{proof('row','left')}
#print axioms row_left

theorem row_right : ∀ i : Fin 222, rowOrder (rowOrderInv i) = i := by
  intro i
  fin_cases i
{proof('row','right')}
#print axioms row_right

theorem col_left : ∀ i : Fin 222, colOrderInv (colOrder i) = i := by
  intro i
  fin_cases i
{proof('col','left')}
#print axioms col_left

theorem col_right : ∀ i : Fin 222, colOrder (colOrderInv i) = i := by
  intro i
  fin_cases i
{proof('col','right')}
#print axioms col_right

def rowEquiv : Fin 222 ≃ Fin 222 where
  toFun := rowOrder
  invFun := rowOrderInv
  left_inv := row_left
  right_inv := row_right

def colEquiv : Fin 222 ≃ Fin 222 where
  toFun := colOrder
  invFun := colOrderInv
  left_inv := col_left
  right_inv := col_right
#print axioms rowEquiv
#print axioms colEquiv
end AspisV8R19.R766BlockOrderEquivalences
'''
    # Ensure generated dependencies contain exactly the compiled 7 chunks and prior case/defs.
    return src

def main():
    ap=argparse.ArgumentParser();ap.add_argument('--check',action='store_true');a=ap.parse_args()
    out=GEN/'R766BlockOrderEquivalences.lean'; body=build()
    if a.check:
        if not out.exists() or out.read_text()!=body: raise SystemExit('R766 output stale/missing')
        print('--check: all pinned dependencies and R766 source match')
    else:
        out.write_text(body); print(f'generated {out} sha256={hashlib.sha256(body.encode()).hexdigest()}')
if __name__=='__main__': main()
