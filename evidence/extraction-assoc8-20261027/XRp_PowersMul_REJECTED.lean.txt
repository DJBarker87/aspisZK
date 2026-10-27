import XRo_Join_Installed
open Aeneas Aeneas.Std Result
set_option autoImplicit false
namespace XRp_PowersMul
open XRo_Join_Carriers
abbrev TQ := AspisR1PowersConcreteMul.SourceQM
def toQ (q : E.Q) : TQ := ⟨⟨q.c0.a,q.c0.b⟩,⟨q.c1.a,q.c1.b⟩⟩

theorem add (a b : E.Q) :
    mapR toQ (XRn_Join_Field.field.QM31.add a b) =
      AspisR1CurrentWideMul.field.QM31.add (toQ a) (toQ b) := by
  rfl

theorem sub (a b : E.Q) :
    mapR toQ (XRn_Join_Field.field.QM31.sub a b) =
      AspisR1CurrentWideMul.field.QM31.sub (toQ a) (toQ b) := by
  rfl

theorem mul (a b : E.Q) :
    mapR toQ (XRn_Join_Field.field.QM31.mul a b) =
      AspisR1CurrentWideMul.field.QM31.mul (toQ a) (toQ b) := by
  rfl

#print axioms add
#print axioms sub
#print axioms mul
end XRp_PowersMul
