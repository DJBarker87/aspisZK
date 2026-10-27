import XRu_RowRun
import ExtractedCurrentReducer
open Aeneas Aeneas.Std Result ControlFlow XRn_Join_Release
set_option autoImplicit false
namespace XRu_RowFold
open XRu_RowShape
abbrev It := core.slice.iter.IterMut U64
abbrev Back := It → It
def row (a b c d : U64) : Row := Array.make 4#usize [a,b,c,d]
def it (a b c d : U64) (n : Nat) : It := ⟨(row a b c d).to_slice,n⟩
def put (n : Nat) (v : U64) : Back := fun r => {r with slice:=r.slice.setAtNat n v}
def step (s : It × Back) := verifier.update_residue_row_loop1.body s.1 s.2
theorem fold_bind {T : Type} (x : U64) (k : U64 → Result T) :
 (do
  let masked ← lift (x &&& 2147483647#u64)
  let shifted ← x >>> 31#i32
  let value ← masked+shifted
  k value) = (do let value ← AspisR1.ExtractedCurrentReducer.foldExecution x; k value) := by
 simp only [AspisR1.ExtractedCurrentReducer.foldExecution,
  AspisR1.ExtractedCurrentReducer.mask64,AspisR1.ExtractedCurrentReducer.mask32,
  lift,bind_tc_ok,bind_assoc_eq]
 rfl
#print axioms fold_bind
theorem step0 (a b c d v : U64) (back : Back)
 (fold : AspisR1.ExtractedCurrentReducer.foldExecution a=ok v) :
 step (it a b c d 0,back)=ok (@ControlFlow.cont (It × Back) Back (it a b c d 1,fun r => back (put 0 v r))) := by
 unfold step verifier.update_residue_row_loop1.body
 simp only [core.slice.iter.IteratorIterMut.next,it,row]
 change (do
  let masked ← lift (a &&& 2147483647#u64)
  let shifted ← a >>> 31#i32
  let value ← masked+shifted
  ok (@ControlFlow.cont (It × Back) Back (it a b c d 1,fun r => back (put 0 value r)))) = _
 rw [fold_bind,fold]
 rfl
#print axioms step0
theorem step1 (a b c d v : U64) (back : Back)
 (fold : AspisR1.ExtractedCurrentReducer.foldExecution b=ok v) :
 step (it a b c d 1,back)=ok (@ControlFlow.cont (It × Back) Back (it a b c d 2,fun r => back (put 1 v r))) := by
 unfold step verifier.update_residue_row_loop1.body
 simp only [core.slice.iter.IteratorIterMut.next,it,row]
 change (do
  let masked ← lift (b &&& 2147483647#u64)
  let shifted ← b >>> 31#i32
  let value ← masked+shifted
  ok (@ControlFlow.cont (It × Back) Back (it a b c d 2,fun r => back (put 1 value r)))) = _
 rw [fold_bind,fold]
 rfl
#print axioms step1
theorem step2 (a b c d v : U64) (back : Back)
 (fold : AspisR1.ExtractedCurrentReducer.foldExecution c=ok v) :
 step (it a b c d 2,back)=ok (@ControlFlow.cont (It × Back) Back (it a b c d 3,fun r => back (put 2 v r))) := by
 unfold step verifier.update_residue_row_loop1.body
 simp only [core.slice.iter.IteratorIterMut.next,it,row]
 change (do
  let masked ← lift (c &&& 2147483647#u64)
  let shifted ← c >>> 31#i32
  let value ← masked+shifted
  ok (@ControlFlow.cont (It × Back) Back (it a b c d 3,fun r => back (put 2 value r)))) = _
 rw [fold_bind,fold]
 rfl
#print axioms step2
theorem step3 (a b c d v : U64) (back : Back)
 (fold : AspisR1.ExtractedCurrentReducer.foldExecution d=ok v) :
 step (it a b c d 3,back)=ok (@ControlFlow.cont (It × Back) Back (it a b c d 4,fun r => back (put 3 v r))) := by
 unfold step verifier.update_residue_row_loop1.body
 simp only [core.slice.iter.IteratorIterMut.next,it,row]
 change (do
  let masked ← lift (d &&& 2147483647#u64)
  let shifted ← d >>> 31#i32
  let value ← masked+shifted
  ok (@ControlFlow.cont (It × Back) Back (it a b c d 4,fun r => back (put 3 value r)))) = _
 rw [fold_bind,fold]
 rfl
#print axioms step3
theorem stop (a b c d : U64) (back : Back) :
 step (it a b c d 4,back)=ok (.done back) := by
 unfold step verifier.update_residue_row_loop1.body
 simp [core.slice.iter.IteratorIterMut.next,it,row]
#print axioms stop
end XRu_RowFold
