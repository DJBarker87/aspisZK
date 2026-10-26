import R1Z.ProverRw18CopyArray
import R1Z.ProverRw18CopyWide
set_option autoImplicit false
noncomputable section
namespace R1Z.ProverRw18CopyArrayWide
open Aeneas Aeneas.Std ProverRw18FieldMeaning
abbrev W := AspisWideTower.WideExact

def tuple (tag : U32) (values : Array U32 16#usize) : W × (Fin 16 → W) :=
  ProverRw18CopyWide.tuple tag (ProverRw18ArrayValues.elements values)

theorem value (tag : U32) (values : Array U32 16#usize) (lambda : K) :
    algebraMap K W (ProverRw18FieldReference.value tag (Array.to_slice values).val lambda)=
      (R0P.compressPoly (tuple tag values)).eval (algebraMap K W lambda) := by
  change algebraMap K W (ProverRw18FieldReference.value tag values.val lambda)=_
  rw [← ProverRw18ArrayValues.ofFn values]
  exact ProverRw18CopyWide.value tag (ProverRw18ArrayValues.elements values) lambda

#print axioms value
end R1Z.ProverRw18CopyArrayWide
