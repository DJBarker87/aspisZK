import NEI_PushRaw.Funs
import NEI_PushBridge
set_option autoImplicit false
noncomputable section
namespace NEI_PushRawAssociation
open Aeneas Aeneas.Std Result
abbrev RawPower := NEI_PushRaw.aspis_core.field.QM31
abbrev RawBW := NEI_PushRaw.BatchedWeights

def toPower (p : RawPower) : NEG_RowAssociation.Power :=
 ⟨⟨p.c0.a,p.c0.b⟩,⟨p.c1.a,p.c1.b⟩⟩
def fromPower (p : NEG_RowAssociation.Power) : RawPower :=
 ⟨⟨p.c0.a,p.c0.b⟩,⟨p.c1.a,p.c1.b⟩⟩
def toBW (b : RawBW) : NEG_PushActual.BatchedWeights := ⟨b.raw,b.terms⟩
def fromBW (b : NEG_PushActual.BatchedWeights) : RawBW := ⟨b.raw,b.terms⟩

theorem power_roundtrip (p : RawPower) : fromPower (toPower p)=p := by cases p; rfl
theorem power_reverse (p : NEG_RowAssociation.Power) : toPower (fromPower p)=p := by cases p; rfl
theorem bw_roundtrip (b : RawBW) : fromBW (toBW b)=b := by cases b; rfl
theorem bw_reverse (b : NEG_PushActual.BatchedWeights) : toBW (fromBW b)=b := by cases b; rfl

/-- Only nominal carrier transport: both original row loop bodies and the exact
borrow continuation are unchanged. No arithmetic theorem is reproved. -/
theorem row (r : Array U64 4#usize) (p : RawPower) (basis : U32) (flush : Bool) :
 NEI_PushRaw.update_residue_row r p basis flush =
 NEG_PushActual.update_residue_row r (toPower p) basis flush := by rfl

theorem push (b : RawBW) (index : Usize) (p : RawPower) (basis : U32) :
 (do let out ← NEI_PushRaw.BatchedWeights.push b index p basis; ok (toBW out)) =
 NEG_PushActual.BatchedWeights.push (toBW b) index (toPower p) basis := by
 simp only [NEI_PushRaw.BatchedWeights.push,NEG_PushActual.BatchedWeights.push,
   lift,bind_assoc_eq,bind_tc_ok,toBW]
 congr 1
 funext pair
 rcases pair with ⟨a,back⟩
 dsimp only
 rw [row]
 cases NEG_PushActual.update_residue_row a (toPower p) basis
   (decide (b.terms &&& 3#usize=3#usize)) <;> rfl

#print axioms power_roundtrip
#print axioms power_reverse
#print axioms bw_roundtrip
#print axioms bw_reverse
#print axioms row
#print axioms push
end NEI_PushRawAssociation
end
