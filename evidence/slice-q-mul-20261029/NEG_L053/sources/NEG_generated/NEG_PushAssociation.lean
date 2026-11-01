import NEG_PushActual.Funs
import NEG_RowAssociation
set_option autoImplicit false
noncomputable section
namespace NEG_PushAssociation
open Aeneas Aeneas.Std Result
abbrev Power := NEG_RowAssociation.Power

def toOld (b : NEG_PushActual.BatchedWeights) : Port23PUSH.verifier.BatchedWeights :=
  ⟨b.raw,b.terms⟩
def fromOld (b : Port23PUSH.verifier.BatchedWeights) : NEG_PushActual.BatchedWeights :=
  ⟨b.raw,b.terms⟩

theorem emitted (b : NEG_PushActual.BatchedWeights) (index : Usize)
    (p : Power) (basis : U32) :
    NEG_PushActual.BatchedWeights.push b index p basis =
      (do let out ← Port23PUSH.verifier.BatchedWeights.push Port25ARRAY.concrete
            (toOld b) index (NEG_RowAssociation.toOld p) basis
          ok (fromOld out)) := by
  unfold NEG_PushActual.BatchedWeights.push Port23PUSH.verifier.BatchedWeights.push
  have row_eq (row : Array U64 4#usize) (power : Power) (k : U32) (flush : Bool) :
      NEG_PushActual.update_residue_row row power k flush =
      Port23PUSH.verifier.update_residue_row Port25ARRAY.concrete row
        (NEG_RowAssociation.toOld power) k flush := by rfl
  simp only [toOld,fromOld,bind_assoc_eq,row_eq]
  congr 1
  funext phase
  congr 1
  funext pair
  rcases pair with ⟨old,back⟩
  simp only [bind_assoc_eq,bind_tc_ok]
  rfl

theorem source (b : NEG_PushActual.BatchedWeights) (index : Usize)
    (p : Power) (basis : U32) :
    NEG_PushActual.BatchedWeights.push b index p basis =
      (do let out ← S7Kani2OwnedPush.push_owned ⟨b.raw,b.terms⟩ index
            (Port26ROW.toK (NEG_RowAssociation.toOld p)) basis
          ok (⟨out.raw,out.terms⟩ : NEG_PushActual.BatchedWeights)) := by
  rw [emitted,Port26ROW.push_complete]
  simp only [bind_assoc_eq,bind_tc_ok,toOld,fromOld,Port26ROW.toBW,Port26ROW.fromBW]

#print axioms emitted
#print axioms source
end NEG_PushAssociation
end
