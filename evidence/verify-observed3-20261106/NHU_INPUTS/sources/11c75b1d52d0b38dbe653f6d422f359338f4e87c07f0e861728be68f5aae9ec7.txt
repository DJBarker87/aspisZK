import NHU_MaskHelpers
set_option autoImplicit false
open Aeneas Aeneas.Std Result
namespace AspisR1.NHU_Tower
open NHU_MaskHelpers AspisR1.ExtractedMaskTowerAdd
abbrev W := Nat×Nat

def iNative (x : W) : W := (negWord x.2,x.1)
def basisNative (x : W×W) (coordinate : Nat) : W×W :=
 match coordinate with
 | 0 => x
 | 1 => (iNative x.1,iNative x.2)
 | 2 => (rNative x.2.1 x.2.2,x.1)
 | 3 => (iNative (rNative x.2.1 x.2.2),iNative x.1)
 | _ => x

theorem i_eq (x : W) (hx : x.2<2147483647) :
 iNative x=AspisR1.ExtractedMaskTowerBasis.iWords x := by
 unfold iNative AspisR1.ExtractedMaskTowerBasis.iWords
 rw [negWord_eq x.2 hx]
 rfl

theorem basis_eq (x : W×W)
 (h0 : x.1.1<2147483647 ∧ x.1.2<2147483647)
 (h1 : x.2.1<2147483647 ∧ x.2.2<2147483647)
 (coordinate : Nat) (bound : coordinate<4) :
 basisNative x coordinate=AspisR1.ExtractedMaskTowerBasis.basisWords x coordinate := by
 have cases : coordinate=0 ∨ coordinate=1 ∨ coordinate=2 ∨ coordinate=3 := by omega
 rcases cases with h|h|h|h <;> subst coordinate
 · rfl
 · exact Prod.ext (i_eq x.1 h0.2) (i_eq x.2 h1.2)
 · exact Prod.ext (rNative_eq _ _ h1.1 h1.2) rfl
 · change (iNative (rNative x.2.1 x.2.2),iNative x.1)=_
   rw [rNative_eq _ _ h1.1 h1.2]
   apply Prod.ext
   · apply i_eq
     change (x.2.1+(x.2.2+x.2.2)%2147483647)%2147483647<2147483647
     omega
   · exact i_eq x.1 h0.2

theorem result (x : QM) (canonical : CanonicalQM x) (coordinate : Usize)
 (bound : coordinate.val<4) :
 ∃ out,AspisR1SelectedMaskProbe.state_only_hiding.mul_tower_basis x coordinate=ok out ∧
 CanonicalQM out ∧ wordsQM out=basisNative (wordsQM x) coordinate.val := by
 obtain ⟨out,call,canon,words⟩:=
  AspisR1.ExtractedMaskTowerBasis.current_mul_tower_basis_words x coordinate canonical bound
 refine ⟨out,call,canon,words.trans ?_⟩
 exact (basis_eq (wordsQM x) canonical.1 canonical.2 coordinate.val bound).symm

#print axioms i_eq
#print axioms basis_eq
#print axioms result
end AspisR1.NHU_Tower
