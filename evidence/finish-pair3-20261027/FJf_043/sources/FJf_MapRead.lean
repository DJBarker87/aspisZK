import FJf_ArraySlots
import FJc_ReadSlot
set_option autoImplicit false
namespace AspisR1.FJf_MapRead
open Aeneas Aeneas.Std Result

theorem source {A B : Type} {N : Usize} (f : A → B) (a : Array A N) (i : Usize) (b : B)
    (run : Array.index_usize (FIn_WeightsInstall.mapArray f a) i=ok b) :
    ∃ x,Array.index_usize a i=ok x ∧ f x=b := by
  have hs := FJc_ReadSlot.slot _ _ _ run
  change (a.val.map f)[i.val]?=some b at hs
  rw [List.getElem?_map] at hs
  cases hh : a.val[i.val]? with
  | none => simp only [hh,Option.map_none] at hs;cases hs
  | some x =>
    simp only [hh,Option.map_some] at hs
    refine ⟨x,?_,Option.some.inj hs⟩
    unfold Array.index_usize
    simp only [hh]
#print axioms source
end AspisR1.FJf_MapRead
