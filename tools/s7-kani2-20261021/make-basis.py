from pathlib import Path
import hashlib,json,sys
R=Path(__file__).resolve().parents[2];B=R/'docs/research/100bit-spend-path-20261013'
p=B/'evidence/s7-kani-20261021/extraction/generated/S7OwnedP6/Funs.lean';s=p.read_text();a=s.index('def basis_block_owned\n');b=s.index('partial_fixpoint',a)+len('partial_fixpoint');original=s[a:b]
body=original.replace('aspis_core.field.M31','U32').replace('def basis_block_owned\n','def basis_block_owned (multiply : U32 → U32 → Result U32)\n').replace('let value ← U32.mul m node','let value ← multiply m node').replace('basis_block_owned basis1 node','basis_block_owned multiply basis1 node')
step=body[body.index('    let m ←'):body.index('    let i1 ←')]
header='''import S7Kani2AccumulatorLoop

/- Exact emitted basis-block recurrence; the sole external primitive is an
explicit parameter. This isolates source loop control from field arithmetic. -/
set_option autoImplicit false
namespace S7Kani2BasisLoop
open Aeneas Aeneas.Std Result
abbrev Basis := Array U32 256#usize

def step (multiply : U32 → U32 → Result U32) (node : U32) (n j : Usize)
    (basis : Basis) : Result Basis := do
'''+ '\n'.join(l[2:] for l in step.rstrip().splitlines())+'''
  ok basis1

'''
tail='''
def iterate (f : Usize → Basis → Result Basis) : Nat → Usize → Basis → Result Basis
 | 0,_,basis => ok basis
 | fuel+1,j,basis => do
     let basis1 ← f j basis
     let j1 ← j + 1#usize
     iterate f fuel j1 basis1

theorem extracted_basis_block_composition (multiply : U32 → U32 → Result U32)
    (basis : Basis) (node : U32) (n j : Usize) (fuel : Nat)
    (hn : n.val≤128) (remaining : j.val+fuel=n.val) :
    basis_block_owned multiply basis node n j =
      iterate (step multiply node n) fuel j basis := by
  induction fuel generalizing j basis with
  | zero =>
      have stop : j ≥ n := by scalar_tac
      rw [basis_block_owned]
      simp only [stop,if_pos,iterate]
  | succ fuel ih =>
      have running : ¬ j ≥ n := by scalar_tac
      obtain ⟨j1,hj1,hval⟩ := S7Kani2AccumulatorLoop.increment j (by omega)
      rw [basis_block_owned]
      simp only [running,if_false,iterate,step,bind_assoc_eq,bind_tc_ok]
      congr 1
      funext m
      congr 1
      funext value
      congr 1
      funext i
      congr 1
      funext basis1
      simp only [hj1,bind_tc_ok]
      exact ih basis1 j1 (by omega)

/-- Every source basis write lies in the 256-cell allocation. -/
theorem basis_write_bounds (n j : Nat) (hn : n≤128) (hj : j<n) :
    j<256 ∧ n+j<256 ∧ j+1≤128 := by omega

#print axioms extracted_basis_block_composition
#print axioms basis_write_bounds
end S7Kani2BasisLoop
'''
text=header+body+'\n'+tail
out=B/'lean/S7Kani2BasisLoop.lean'
if '--check' in sys.argv:assert out.read_text()==text
else:out.write_text(text)
(B/'evidence/s7-kani2-20261021/basis-binding.json').write_text(json.dumps(dict(source=str(p.relative_to(R)),source_sha256=hashlib.sha256(p.read_bytes()).hexdigest(),declaration_sha256=hashlib.sha256(original.encode()).hexdigest(),edits='Rename M31 to exact U32 carrier; explicitly parameterise multiply; parameter threaded through recursive call. No body operation removed.'),indent=2)+'\n')
