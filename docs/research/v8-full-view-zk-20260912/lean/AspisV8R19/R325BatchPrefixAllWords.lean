import AspisV8R19.R324BatchPrefixComplete

/-! Universal all-word selected prefix-loop Result correspondence.
`sourceWord` is a total mathematical indexing function. Its arbitrary default
is unreachable on every active iteration, as proved by sourceWord_read. -/
set_option autoImplicit false
namespace AspisV8R19.R325BatchPrefixAllWords
open Aeneas Aeneas.Std Result ControlFlow
open AspisV8R19.R319BatchPrefixStepExecution
open AspisV8R19.R324BatchPrefixComplete
open AspisR318BatchPrefixRaw.circle_norm.joined_inverse.line_norm.r110_norm
noncomputable section

def sourceWord (xs : Slice U32) (j : Nat) : U32 :=
  xs.val[j]?.getD 0#u32

theorem sourceWord_read (xs : Slice U32) (j : Nat)
    (h : j < xs.val.length) :
    xs.val[j]? = some (sourceWord xs j) := by
  simp only [sourceWord, List.getElem?_eq_getElem h, Option.getD_some]

theorem batch_loop0_all_words (iter : PrefixIter) (px : alloc.vec.Vec U32) :
    batch_loop0 iter px =
      prefixResult (sourceWord iter.slice) iter.i (iter.slice.val.length - iter.i) px := by
  by_cases h : iter.i ≤ iter.slice.val.length
  · exact batch_loop0_complete _ _ iter px (by omega)
      (by intro j _ hj; exact sourceWord_read iter.slice j hj)
  · have hstop : iter.slice.val.length ≤ iter.i := by omega
    have hz : iter.slice.val.length - iter.i = 0 := by omega
    rw [hz, batch_loop0, loop.eq_def]
    dsimp only
    rw [body0_done iter px hstop]
    rfl

theorem batch_loop1_all_words (iter : PrefixIter) (py : alloc.vec.Vec U32) :
    batch_loop1 iter py =
      prefixResult (sourceWord iter.slice) iter.i (iter.slice.val.length - iter.i) py := by
  change batch_loop0 iter py = _
  exact batch_loop0_all_words iter py

#print axioms sourceWord_read
#print axioms batch_loop0_all_words
#print axioms batch_loop1_all_words
end
end AspisV8R19.R325BatchPrefixAllWords
