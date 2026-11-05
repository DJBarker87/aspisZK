import NHU_Tower
import NHU_RefCase1
import NHU_RefCase2
import NHU_RefCase3
set_option autoImplicit false
open Aeneas Aeneas.Std Result
namespace AspisR1.NHU_TowerReference
open NHU_RefWords

def referenceWords (x : W×W) (coordinate : Nat) : W×W :=
 match coordinate with
 | 0 => x
 | 1 => (iRef x.1,iRef x.2)
 | 2 => (rRef x.2,x.1)
 | 3 => (iRef (rRef x.2),iRef x.1)
 | _ => x

/-- The failed large rewrite is split into independently checked cases. No
field recurrence, product or concrete large modulus is normalized here. -/
theorem correspondence (x : W×W) (left : Good x.1) (right : Good x.2)
 (coordinate : Nat) (bound : coordinate<4) :
 referenceWords x coordinate=ExtractedMaskTowerBasis.basisWords x coordinate := by
 have cases : coordinate=0 ∨ coordinate=1 ∨ coordinate=2 ∨ coordinate=3 := by omega
 rcases cases with h|h|h|h <;> subst coordinate
 · rfl
 · exact NHU_RefCase1.result x left right
 · exact NHU_RefCase2.result x right
 · exact NHU_RefCase3.result x left right

theorem result (x : NHU_Tower.QM) (canonical : ExtractedMaskTowerAdd.CanonicalQM x)
 (coordinate : Usize) (bound : coordinate.val<4) :
 ∃ out,AspisR1SelectedMaskProbe.state_only_hiding.mul_tower_basis x coordinate=ok out ∧
 ExtractedMaskTowerAdd.CanonicalQM out ∧
 ExtractedMaskTowerAdd.wordsQM out=referenceWords (ExtractedMaskTowerAdd.wordsQM x) coordinate.val := by
 obtain ⟨out,call,canon,words⟩:=NHU_Tower.result x canonical coordinate bound
 exact ⟨out,call,canon,words.trans
  (correspondence _ canonical.1 canonical.2 coordinate.val bound).symm⟩
#print axioms correspondence
#print axioms result
end AspisR1.NHU_TowerReference
