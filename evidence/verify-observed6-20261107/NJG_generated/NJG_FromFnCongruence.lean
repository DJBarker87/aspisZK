import NJG_FinishBody
import OraclePortStdBuilder
set_option autoImplicit false
namespace AspisR1.NJG_FromFnCongruence
open Aeneas Aeneas.Std Result OraclePortStdBuilder

theorem indices_bound (N : Usize) (i : Usize) (member : i∈indices N) : i.val<N.val := by
 simp only [indices,List.mem_ofFn] at member
 obtain ⟨j,rfl⟩:=member
 exact j.isLt

/-- Exact state-threaded callback replacement on the visited domain only;
all errors and divergence remain, and no callback outside the range is used. -/
theorem loop {T C : Type} (N : Usize) (f g : core.ops.function.FnMut C Usize T)
 (same : ∀ (c : C) (i : Usize),i.val<N.val → f.call_mut c i=g.call_mut c i)
 (is : List Usize) (bounds : ∀ i,i∈is → i.val<N.val) (c : C) :
 fromFnLoop f is c=fromFnLoop g is c := by
 induction is generalizing c with
 | nil=>rfl
 | cons i is ih=>
   simp only [fromFnLoop,same c i (bounds i (by simp))]
   apply congrArg (fun k=>(g.call_mut c i >>= k))
   funext pair
   rcases pair with ⟨value,next⟩
   rw [ih (by intro j hj;exact bounds j (by simp [hj])) next]

theorem source {T C : Type} (N : Usize) (f g : core.ops.function.FnMut C Usize T)
 (same : ∀ (c : C) (i : Usize),i.val<N.val → f.call_mut c i=g.call_mut c i) (c : C) :
 fromFn N f c=fromFn N g c := by
 unfold fromFn
 rw [loop N f g same (indices N) (indices_bound N) c]

#print axioms indices_bound
#print axioms loop
#print axioms source
end AspisR1.NJG_FromFnCongruence
