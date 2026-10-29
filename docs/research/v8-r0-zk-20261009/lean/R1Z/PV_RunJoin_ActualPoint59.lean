import R1Z.PV_RunJoin_OpeningImages54
set_option autoImplicit false
noncomputable section
namespace R1Z.PV_RunJoin_ActualPoint59
attribute [local instance] Classical.propDecidable

def point {K : Type} [Field K] (x y : K) : AspisR0.ChordGeometry.Point K :=
  if h : x^2+y^2=1 then ⟨(x,y),h⟩ else ⟨(1,0),by simp⟩

theorem first {K : Type} [Field K] (x y : K) (h : x^2+y^2=1) :
    (point x y).val=(x,y) := by simp only [point,dif_pos h]

#print axioms point
#print axioms first
end R1Z.PV_RunJoin_ActualPoint59
