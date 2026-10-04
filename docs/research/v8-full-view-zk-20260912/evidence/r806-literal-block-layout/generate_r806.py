import pathlib,json,hashlib
p=pathlib.Path('.r21-scratch/r724-h1-left-inverse-certificate/evidence/attempt-2-success/certificate.json');assert hashlib.sha256(p.read_bytes()).hexdigest()=='d170dc15f81b0aac68da6cb9291e9907ad72e1738cf3a6b6fd7faf9e32a951f4';d=json.loads(p.read_text());sizes=[b['dimension'] for b in d['blocks']];assert len(sizes)==41 and sum(sizes)==222;offsets=[];off=0
for n in sizes:offsets.append(off);off+=n
labels=[k for k,n in enumerate(sizes) for j in range(n)];assert len(labels)==222
s='''import Mathlib.Data.Fintype.Card
import Mathlib.Tactic

set_option autoImplicit false
set_option maxRecDepth 32768
set_option maxHeartbeats 800000
namespace AspisV8R19.R806LiteralBlockLayout

-- Literal index tables only: no field arithmetic or certificate inversion is evaluated.
def blockSize (k : Fin 41) : Nat :=
  match k.val with
'''+''.join(f'  | {k} => {n}\n' for k,n in enumerate(sizes[:-1]))+f'  | _ => {sizes[-1]}\n\n'
s+='def blockOffset (k : Fin 41) : Nat :=\n  match k.val with\n'+''.join(f'  | {k} => {n}\n' for k,n in enumerate(offsets[:-1]))+f'  | _ => {offsets[-1]}\n\n'
s+='def blockLabel (i : Fin 222) : Fin 41 :=\n  match i.val with\n'+''.join(f'  | {i} => {k}\n' for i,k in enumerate(labels[:-1]))+f'  | _ => {labels[-1]}\n\n'
s+='''theorem blockSize_pos (k : Fin 41) : 0 < blockSize k := by revert k; decide

theorem block_end_bound (k : Fin 41) : blockOffset k + blockSize k ≤ 222 := by
  revert k
  decide

theorem blockLabel_bounds (i : Fin 222) (k : Fin 41) :
    blockLabel i = k ↔ blockOffset k ≤ i.val ∧ i.val < blockOffset k + blockSize k := by
  revert i k
  decide

def flatIndex (k : Fin 41) (t : Fin (blockSize k)) : Fin 222 :=
  ⟨blockOffset k + t.val, by have := block_end_bound k; have := t.isLt; omega⟩

theorem blockLabel_flatIndex (k : Fin 41) (t : Fin (blockSize k)) :
    blockLabel (flatIndex k t) = k := by
  apply (blockLabel_bounds _ _).mpr
  simp only [flatIndex, Fin.val_mk]
  have := t.isLt
  omega

def fiberEquiv (k : Fin 41) : Fin (blockSize k) ≃ {i : Fin 222 // blockLabel i = k} where
  toFun t := ⟨flatIndex k t, blockLabel_flatIndex k t⟩
  invFun i := ⟨i.val.val - blockOffset k, by
    have := (blockLabel_bounds i.val k).mp i.property
    omega⟩
  left_inv t := by
    apply Fin.ext
    simp only [flatIndex, Fin.val_mk]
    omega
  right_inv i := by
    apply Subtype.ext
    apply Fin.ext
    simp only [flatIndex, Fin.val_mk]
    have := (blockLabel_bounds i.val k).mp i.property
    omega

#print axioms blockSize_pos
#print axioms block_end_bound
#print axioms blockLabel_bounds
#print axioms blockLabel_flatIndex
#print axioms fiberEquiv
end AspisV8R19.R806LiteralBlockLayout
'''
pathlib.Path('.r21-scratch/R806LiteralBlockLayout.lean').write_text(s);print('generated block dimensions',sizes,'sourceSHA',hashlib.sha256(s.encode()).hexdigest())
