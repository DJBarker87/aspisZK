import RPu_FJn_EqualityMap
import RPu_FIz_ConcretePack
import RPu_FJk_CopyRowTransport
set_option autoImplicit false
noncomputable section
namespace AspisR1.FJn_EqualityArrays
open Aeneas Aeneas.Std
open FIv_NativeValue (K)
open FIw_ArrayValue (decoded)
open FIz_ConcretePack (embed)
attribute [local irreducible] R0P.SemSource.eqValue
theorem mapped (a : Array FIq_Native.field.QM31 10#usize) :
    (fun i : Fin 10=>embed (FIv_NativeArray.value a i.val))=(fun i=>embed (decoded a i)) := by
  funext i
  exact congrArg embed (FJk_CopyRowTransport.cell a i)
theorem value (a b : Array FIq_Native.field.QM31 10#usize) :
    embed (R0P.SemSource.eqValue (fun i : Fin 10=>FIv_NativeArray.value a i.val)
      (fun i : Fin 10=>FIv_NativeArray.value b i.val))=
      R0P.SemSource.eqValue (fun i=>embed (decoded a i)) (fun i=>embed (decoded b i)) := by
  exact (FJn_EqualityMap.value embed _ _).trans (congrArg₂ R0P.SemSource.eqValue (mapped a) (mapped b))
#print axioms mapped
#print axioms value
end AspisR1.FJn_EqualityArrays
end
