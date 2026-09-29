#!/usr/bin/env python3
"""Pin the actual T163 table; prove its fixed tail symbolically, not by replay.

The finite preflight touches only 479 affected-range indices, using 32-entry
lookup blocks. The 545-coordinate identity tail is not enumerated in Lean.
"""
import argparse,hashlib,json,re
from pathlib import Path
p=argparse.ArgumentParser();p.add_argument('--check',action='store_true');a=p.parse_args()
root=Path(__file__).resolve().parent.parent
relative='docs/research/v8-no-work-100-20260907/experiments/r17_basis_tables.rs'
src=root/'evidence/r36-source-residual-model/source'/relative
pins=json.loads((root/'evidence/r43-high-query-witness/rust-i/r18-stage.json').read_text())
digest=hashlib.sha256(src.read_bytes()).hexdigest();assert pins['files'][relative]==digest
text=src.read_text()
order=[int(x.strip())for x in re.search(r'ORDER:.*?= \[(.*?)\];',text,re.S).group(1).split(',')]
inactive=[x.strip()=='true'for x in re.search(r'INACTIVE:.*?= \[(.*?)\];',text,re.S).group(1).split(',')]
assert len(order)==len(inactive)==1024 and sorted(order)==list(range(1024))
assert order[479:]==list(range(479,1024)) and inactive[1023]
assert sum(i!=v for i,v in enumerate(order))==163
inverse=[0]*1024
for j,v in enumerate(order):inverse[v]=j
def blocks(xs):return [xs[i:i+32]for i in range(0,len(xs),32)]
out=f'''/- Generated from source table SHA256 {digest}.
Only small index lookups are reduced. The fixed tail uses a symbolic lemma. -/
import AspisV8R19.ResidualPins
namespace AspisR19.T163SourceTable
def forwardBlocks : List (List Nat) := {blocks(order[:479])!r}
def inverseBlocks : List (List Nat) := {blocks(inverse[:479])!r}
def inactiveBlocks : List (List Bool) := {str(blocks(inactive)).lower()}
def forward (j : Nat) : Nat :=
  if j<479 then (forwardBlocks.getD (j/32) []).getD (j%32) 0 else j
def backward (j : Nat) : Nat :=
  if j<479 then (inverseBlocks.getD (j/32) []).getD (j%32) 0 else j
def isInactive (j : Fin 1024) : Bool :=
  (inactiveBlocks.getD (j.val/32) []).getD (j.val%32) false

theorem small_certificate : ∀ b : Fin 15, ∀ o : Fin 32,
    let j := 32*b.val+o.val
    j<479 → forward j<479 ∧ backward j<479 ∧
      backward (forward j)=j ∧ forward (backward j)=j := by decide

theorem small_facts (j : Nat) (hj : j<479) :
    forward j<479 ∧ backward j<479 ∧
      backward (forward j)=j ∧ forward (backward j)=j := by
  have h := small_certificate ⟨j/32,by omega⟩ ⟨j%32,by omega⟩
  have he : 32*(j/32)+j%32=j := by omega
  dsimp only at h
  rw [he] at h
  exact h hj

theorem forward_bounds (j : Fin 1024) : forward j.val<1024 := by
  by_cases h : j.val<479
  · have := (small_facts j.val h).1; omega
  · simpa [forward,h] using j.isLt
theorem backward_bounds (j : Fin 1024) : backward j.val<1024 := by
  by_cases h : j.val<479
  · have := (small_facts j.val h).2.1; omega
  · simpa [backward,h] using j.isLt
theorem backward_forward (j : Nat) : backward (forward j)=j := by
  by_cases h : j<479
  · exact (small_facts j h).2.2.1
  · simp [forward,backward,h]
theorem forward_backward (j : Nat) : forward (backward j)=j := by
  by_cases h : j<479
  · exact (small_facts j h).2.2.2
  · simp [forward,backward,h]

def order : Fin 1024 ≃ Fin 1024 where
  toFun j := ⟨forward j.val,forward_bounds j⟩
  invFun j := ⟨backward j.val,backward_bounds j⟩
  left_inv j := Fin.ext (backward_forward j.val)
  right_inv j := Fin.ext (forward_backward j.val)
def inactive : Finset (Fin 1024) := Finset.univ.filter (fun j => isInactive j)
theorem pivot_fixed : order (1023 : Fin 1024)=1023 := by decide
theorem pivot_inactive : (1023 : Fin 1024) ∈ inactive := by
  exact Finset.mem_filter.mpr ⟨Finset.mem_univ _,by decide⟩
theorem residual_order_agrees (i : Fin 111) :
    (order ⟨i.val,by omega⟩).val=ResidualPins.order i := by
  revert i; decide
theorem residual_inactive_agrees (i : Fin 111) :
    isInactive (order ⟨i.val,by omega⟩)=ResidualPins.inactive i := by
  revert i; decide

#print axioms small_certificate
#print axioms small_facts
#print axioms forward_bounds
#print axioms backward_bounds
#print axioms backward_forward
#print axioms forward_backward
#print axioms pivot_fixed
#print axioms pivot_inactive
#print axioms residual_order_agrees
#print axioms residual_inactive_agrees
end AspisR19.T163SourceTable
'''
dest=root/'lean/AspisV8R19/T163SourceTable.lean'
if a.check:assert dest.read_text()==out
else:
    dest.write_text(out)
print(json.dumps({'status':'PASS','mode':'check'if a.check else'write','source_sha256':digest,
                  'changed_coordinates':163,'symbolic_fixed_tail':545,'theorems':10}))
