import GeometryStoredPoint
set_option autoImplicit false
open Aeneas Aeneas.Std Result
namespace AspisR1CurrentWide.Proof
private theorem inverse_congr {F : Type} [Inv F] {a b : F} (h : a=b) : a⁻¹=b⁻¹ := congrArg Inv.inv h

theorem stored_denominators_x {q : U32} (g : StoredGeometryPoint q) :
    (storedDenominators g).getD 2 0 = storedLineX g := by rfl
theorem stored_denominators_y {q : U32} (g : StoredGeometryPoint q) :
    (storedDenominators g).getD 3 0 = storedLineY g := by rfl
theorem stored_denominators_z {q : U32} (g : StoredGeometryPoint q) :
    (storedDenominators g).getD 4 0 = storedLineZ g := by rfl

theorem stored_inverse_x {q : U32} (g : StoredGeometryPoint q) :
    ((storedDenominators g).getD 2 0)⁻¹ = (storedLineX g)⁻¹ := inverse_congr (stored_denominators_x g)
theorem stored_inverse_y {q : U32} (g : StoredGeometryPoint q) :
    ((storedDenominators g).getD 3 0)⁻¹ = (storedLineY g)⁻¹ := inverse_congr (stored_denominators_y g)
theorem stored_inverse_z {q : U32} (g : StoredGeometryPoint q) :
    ((storedDenominators g).getD 4 0)⁻¹ = (storedLineZ g)⁻¹ := inverse_congr (stored_denominators_z g)

theorem stored_inverse_y_unique {q : U32} (a b : StoredGeometryPoint q) :
    (storedLineY a)⁻¹ = (storedLineY b)⁻¹ := congrArg (fun g => (storedLineY g)⁻¹) (stored_point_unique a b)
theorem stored_inverse_z_unique {q : U32} (a b : StoredGeometryPoint q) :
    (storedLineZ a)⁻¹ = (storedLineZ b)⁻¹ := congrArg (fun g => (storedLineZ g)⁻¹) (stored_point_unique a b)
#print axioms stored_inverse_x
#print axioms stored_inverse_y
#print axioms stored_inverse_z
#print axioms stored_inverse_y_unique
#print axioms stored_inverse_z_unique
end AspisR1CurrentWide.Proof
