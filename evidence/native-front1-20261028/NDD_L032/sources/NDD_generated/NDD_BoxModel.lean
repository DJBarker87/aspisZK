import FIn_WeightsFuns
set_option autoImplicit false
open Aeneas Aeneas.Std Result
namespace NDD_BoxModel
open FIn_WeightsExtract
/-- The model erases Box ownership/allocation; this is a model constructor fact,
not an allocator or native Box correspondence theorem. -/
theorem parts (v : FInVariant)
    (f : Array (Array (Array field.QM31 4#usize) 5#usize) 5#usize)
    (p : Array (Array field.QM31 10#usize) 3#usize) (e : Array field.QM31 2#usize) :
    Weights.box_from_parts v f p e = ok (⟨v,f,p,e⟩ : Weights) := rfl
#print axioms parts
end NDD_BoxModel
