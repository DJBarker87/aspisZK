import XSa_RawWrap
open Aeneas Aeneas.Std Result
set_option autoImplicit false
namespace XSa_RawFolds

theorem uv (c d g h : Nat)
 (hc : c≤2147483646) (hd : d≤2147483646) (hg : g≤2147483646) (hh : h≤2147483646) :
 XRn_Join_partial (XRn_Join_sub64 (XRn_Join_wrap64 (c*g+2147483647*2147483647)) (d*h)) =
   AspisR1BatchedFoldArithmetic.fold (c*g+2147483647*2147483647-d*h) ∧
 XRn_Join_partial (XRn_Join_wrap64 (c*h+d*g)) =
   AspisR1BatchedFoldArithmetic.fold (c*h+d*g) := by
 have guards := AspisR1S5CurrentRepin.canonical_raw_range_guards 0 0 c d 0 0 g h
   (by omega) (by omega) hc hd (by omega) (by omega) hg hh
 dsimp only at guards
 norm_num only [Nat.reducePow,Nat.reduceSub,Nat.reduceMul] at guards
 rcases guards with ⟨hcg,hdh,hch,_⟩
 constructor
 · rw [XSa_RawWrap.wrap _ hcg,XSa_RawWrap.sub _ _ hcg hdh,
     XSa_RawWrap.fold_word _ (by omega)]
 · rw [XSa_RawWrap.wrap _ hch,XSa_RawWrap.fold_word _ hch]

#print axioms uv
end XSa_RawFolds
