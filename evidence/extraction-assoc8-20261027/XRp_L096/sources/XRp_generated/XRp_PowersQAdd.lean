import XRp_PowersComplex
open Aeneas Aeneas.Std Result
set_option autoImplicit false
namespace XRp_PowersQAdd
open XRo_Join_Carriers XRo_Join_ResultTransport XRp_PowersComplex
abbrev EQ := XRn_Join_Field.field.QM31
abbrev TQ := AspisR1Qm31ArithmeticProbe.field.QM31
def toQ (q : EQ) : TQ := ⟨toC q.c0,toC q.c1⟩
def CanonicalQ (q : EQ) := Canonical q.c0 ∧ Canonical q.c1

theorem add (a b : EQ) (ha : CanonicalQ a) (hb : CanonicalQ b) :
    mapR toQ (XRn_Join_Field.field.QM31.add a b) =
      AspisR1CurrentWideMul.field.QM31.add (toQ a) (toQ b) := by
  unfold XRn_Join_Field.field.QM31.add AspisR1CurrentWideMul.field.QM31.add
    AspisR1Qm31ArithmeticProbe.field.QM31.add
  change mapR toQ (do
    let x ← XRn_Join_Field.field.CM31.add a.c0 b.c0
    let y ← XRn_Join_Field.field.CM31.add a.c1 b.c1
    ok (⟨x,y⟩ : EQ)) = (do
      let x ← AspisR1Qm31ArithmeticProbe.field.CM31.add (toC a.c0) (toC b.c0)
      let y ← AspisR1Qm31ArithmeticProbe.field.CM31.add (toC a.c1) (toC b.c1)
      ok (⟨x,y⟩ : TQ))
  rw [← XRp_PowersComplex.add a.c0 b.c0 ha.1 hb.1,
    ← XRp_PowersComplex.add a.c1 b.c1 ha.2 hb.2]
  simp only [mapR_bind,bind_map,map_ok]
  rfl

#print axioms add
end XRp_PowersQAdd
