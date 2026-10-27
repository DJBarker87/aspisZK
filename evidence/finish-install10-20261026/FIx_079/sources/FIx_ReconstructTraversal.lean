import FIx_ReconstructStep
set_option autoImplicit false
noncomputable section
namespace AspisR1.FIx_ReconstructTraversal
open Aeneas Aeneas.Std Result FIq_Native
open FIv_NativeArithmetic (NQ)
open FIx_ReconstructStep (Capture callback)
abbrev Iter := core.slice.iter.Iter NQ

def fold (it : Iter) (acc : NQ) (c : Capture) : Result NQ :=
  revFold (core.slice.iter.Iter.Insts.CoreIterTraitsDouble_endedDoubleEndedIteratorSharedT NQ)
    callback it acc c

def slice (xs : List NQ) (bound : xs.length≤Usize.max) : Slice NQ := ⟨xs,bound⟩

theorem nil (acc : NQ) (c : Capture) : fold ⟨slice [] (by simp),0⟩ acc c=ok acc := by
  rw [fold,revFold]
  simp only [core.slice.iter.Iter.Insts.CoreIterTraitsDouble_endedDoubleEndedIteratorSharedT,
    core.slice.iter.Iter.Insts.CoreIterTraitsDouble_endedDoubleEndedIteratorSharedT.next_back,slice]
  rfl

theorem append (xs : List NQ) (x acc : NQ) (c : Capture)
    (bound : (xs++[x]).length≤Usize.max) :
    fold ⟨slice (xs++[x]) bound,0⟩ acc c=(do
      let (next,c') ← callback.call_mut c (acc,x)
      fold ⟨slice xs (by have h:=bound;simp only [List.length_append,List.length_singleton] at h;omega),0⟩ next c') := by
  rw [fold,revFold]
  simp only [core.slice.iter.Iter.Insts.CoreIterTraitsDouble_endedDoubleEndedIteratorSharedT,
    core.slice.iter.Iter.Insts.CoreIterTraitsDouble_endedDoubleEndedIteratorSharedT.next_back,slice,
    List.length_append,List.length_singleton,Nat.zero_lt_succ,↓reduceIte,
    List.getLast?_append,List.getLast?_singleton,(show (xs++[x]).dropLast=xs by simp),Option.some_or,bind_tc_ok]
  rfl
#print axioms nil
#print axioms append
end AspisR1.FIx_ReconstructTraversal
end
