from pathlib import Path
L=Path('docs/research/100bit-spend-path-20261013/lean')
s='''import Port26ROW_Steps
set_option autoImplicit false
noncomputable section
namespace Port26ROW
open Aeneas Aeneas.Std Result ControlFlow
open Port23PUSH Port25ARRAY

theorem range_end :
    core.iter.range.IteratorRange.next core.iter.range.StepUsize ⟨4#usize,4#usize⟩ =
      ok (none,⟨4#usize,4#usize⟩) := by
  obtain ⟨⟨o,it⟩,run,ho,hi⟩ := WP.spec_imp_exists
    (core.iter.range.IteratorRange.next_UScalar_none_spec
      (ty:=.Usize) (cloneInst:=core.clone.CloneUsize)
      (partialOrdInst:=core.cmp.PartialOrdUsize) (by intro a b; rfl)
      ⟨4#usize,4#usize⟩ (by decide))
  subst o
  subst it
  exact run

'''
letters=['a','b','c','d']; powers=['p','q','r','s']
arr=lambda xs: 'Array.make 4#usize ['+','.join(xs)+']'
for j in range(4):
 ys=letters.copy();ys[j]='y'
 s+=f'''theorem add_body{j} (a b c d : U64) (p q r s basis : U32) :
    verifier.update_residue_row_loop0.body ({arr(powers)}) ⟨{j}#usize,4#usize⟩
      ({arr(letters)}) basis =
      (do let y ← addWord {letters[j]} {powers[j]} basis
          ok (cont (⟨{j+1}#usize,4#usize⟩,{arr(ys)},basis))) := by
  rw [verifier.update_residue_row_loop0.body,
    range_next {j}#usize {j+1}#usize (by decide) (by decide)]
  simp only [bind_tc_ok]
  simp only [addWord,bind_assoc_eq]
  rfl

'''
s+='''theorem add_tail4 (row : Row) (basis : U32) (limbs : Array U32 4#usize) :
    verifier.update_residue_row_loop0 ⟨4#usize,4#usize⟩ row basis limbs = ok row := by
  rw [add_unroll]
  simp only [verifier.update_residue_row_loop0.body,range_end,bind_tc_ok]
  rfl

'''
for j in reversed(range(4)):
 out=letters[:j]+['x'+str(i) for i in range(j,4)]
 body='\n'.join('        let x'+str(i)+' ← addWord '+letters[i]+' '+powers[i]+' basis' for i in range(j,4))
 ys=letters.copy();ys[j]='x'
 s+=f'''theorem add_tail{j} (a b c d : U64) (p q r s basis : U32) :
    verifier.update_residue_row_loop0 ⟨{j}#usize,4#usize⟩ ({arr(letters)}) basis
      ({arr(powers)}) =
      (do
{body}
        ok ({arr(out)})) := by
  rw [add_unroll,add_body{j}]
  simp only [bind_assoc_eq,bind_tc_ok]
  congr 1
  funext x
'''
 if j==3:s+='  exact add_tail4 _ _ _\n\n'
 else:s+=f"  exact add_tail{j+1} {' '.join(ys)} p q r s basis\n\n"
for n in ['range_end']+['add_body'+str(i) for i in range(4)]+['add_tail'+str(i) for i in range(5)]: s+='#print axioms '+n+'\n'
s+='end Port26ROW\nend\n'
(L/'Port26ROW_Add.lean').write_text(s)
