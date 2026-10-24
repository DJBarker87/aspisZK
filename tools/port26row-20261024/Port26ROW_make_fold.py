from pathlib import Path
L=Path('docs/research/100bit-spend-path-20261013/lean')
s='''import Port26ROW_Steps
set_option autoImplicit false
noncomputable section
namespace Port26ROW
open Aeneas Aeneas.Std Result ControlFlow
open Port23PUSH Port25ARRAY

def atRow (a b c d : U64) (n : Nat) : Iter U64 :=
  ⟨(Array.make 4#usize [a,b,c,d]).to_slice,n⟩
def put (n : Nat) (y : U64) (im : Iter U64) : Iter U64 :=
  {im with slice := im.slice.setAtNat n y}

theorem fold_unroll (it : Iter U64) (back : Iter U64 → Iter U64) :
    verifier.update_residue_row_loop1 it back =
      (do let step ← verifier.update_residue_row_loop1.body it back
          match step with
          | done out => ok out
          | cont (it,b) => verifier.update_residue_row_loop1 it b) := by
  unfold verifier.update_residue_row_loop1
  rw [loop.eq_def]
  cases h : verifier.update_residue_row_loop1.body it back with
  | ok step => cases step with
    | done out => simp only [h,bind_tc_ok]
    | cont state => rcases state with ⟨it,b⟩; simp only [h,bind_tc_ok]
  | fail e => simp only [h,bind_tc_fail]
  | div => simp only [h,bind_tc_div]

'''
letters=['a','b','c','d']
for j in range(5):
 out='done back' if j==4 else f'cont (atRow a b c d {j+1}, fun im => back (put {j} (folded {letters[j]}) im))'
 s+=f'''theorem fold_body{j} (a b c d : U64) (back : Iter U64 → Iter U64) :
    verifier.update_residue_row_loop1.body (atRow a b c d {j}) back =
      ok ({out}) := by
  rw [fold_body_complete]
  rfl

'''
for j in reversed(range(5)):
 expr='im'
 for i in reversed(range(j,4)):expr=f'put {i} (folded {letters[i]}) ({expr})'
 s+=f'''theorem fold_tail{j} (a b c d : U64) (back : Iter U64 → Iter U64) :
    verifier.update_residue_row_loop1 (atRow a b c d {j}) back =
      ok (fun im => back ({expr})) := by
  rw [fold_unroll,fold_body{j}]
  simp only [bind_tc_ok]
'''
 if j<4:s+=f'  exact fold_tail{j+1} a b c d _\n'
 s+='\n'
s+='''/-- Actual iterator continuation is applied to its original input, then the
existing from_slice readback. All four writes and the entire carrier retained. -/
theorem fold_readback (a b c d : U64) :
    (do let (it,back) ← concrete (Array.make 4#usize [a,b,c,d])
        let f ← verifier.update_residue_row_loop1 it id
        ok (back f)) =
      ok (Array.make 4#usize [folded a,folded b,folded c,folded d]) := by
  change (do let f ← verifier.update_residue_row_loop1 (atRow a b c d 0) id
             ok (Array.from_slice (Array.make 4#usize [a,b,c,d])
               (f (atRow a b c d 0)).slice)) = _
  rw [fold_tail0]
  rfl

'''
for n in ['atRow','put','fold_unroll']+['fold_body'+str(i) for i in range(5)]+['fold_tail'+str(i) for i in range(5)]+['fold_readback']:s+='#print axioms '+n+'\n'
s+='end Port26ROW\nend\n'
(L/'Port26ROW_Fold.lean').write_text(s)
