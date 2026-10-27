import R1Z.PV_CB3_PoleEqualSource
import R1Z.PV_CB3_EqualityBits
import R1Z.PV_CB3_Op258Equal
set_option autoImplicit false
noncomputable section
namespace R1Z.PV_CB3_PoleEqualBridge
open Aeneas Aeneas.Std Result ProverRwFull
local instance : DecidableEq aspis_core.field.QM31 := Classical.decEq _

theorem scalar_eq_iff (a b : U32) : a.bv=b.bv ↔ a=b := by
  constructor
  · intro h
    exact UScalar.eq_of_val_eq (congrArg BitVec.toNat h)
  · intro h; cases h; rfl

theorem scalar_four (a b c d e f g h : U32) :
    (((a ^^^ b) ||| (c ^^^ d)) ||| (e ^^^ f)) ||| (g ^^^ h) = 0#u32 ↔
      a=b ∧ c=d ∧ e=f ∧ g=h := by
  have hz (x : U32) : x=0#u32 ↔ x.bv=0#32 := (scalar_eq_iff x 0#u32).symm
  rw [hz]
  change (((a.bv ^^^ b.bv) ||| (c.bv ^^^ d.bv)) ||| (e.bv ^^^ f.bv)) |||
    (g.bv ^^^ h.bv) = 0#32 ↔ _
  rw [PV_CB3_EqualityBits.four_xor_zero]
  simp only [scalar_eq_iff]

/-- Concrete shipped helper extraction equals the owned reference comparator,
for arbitrary raw limb representatives. This does not close the enclosing loop. -/
theorem source (a b : aspis_core.field.QM31) :
    PV_CB3_PoleEqualSource.ct_pole.equal a b = PV_CB3_Op258Ref.reference.equal a b := by
  have hp : ((((a.c0.a ^^^ b.c0.a) ||| (a.c0.b ^^^ b.c0.b)) |||
      (a.c1.a ^^^ b.c1.a)) ||| (a.c1.b ^^^ b.c1.b) = 0#u32) ↔ a=b := by
    rw [scalar_four]
    rcases a with ⟨⟨a0,a1⟩,⟨a2,a3⟩⟩
    rcases b with ⟨⟨b0,b1⟩,⟨b2,b3⟩⟩
    simp only [aspis_core.field.QM31.mk.injEq,aspis_core.field.CM31.mk.injEq]
    tauto
  simp only [PV_CB3_PoleEqualSource.ct_pole.equal,PV_CB3_Op258Equal.source,lift,bind_tc_ok]
  exact congrArg ok (decide_eq_decide.mpr hp)
#print axioms scalar_eq_iff
#print axioms scalar_four
#print axioms source
end R1Z.PV_CB3_PoleEqualBridge
