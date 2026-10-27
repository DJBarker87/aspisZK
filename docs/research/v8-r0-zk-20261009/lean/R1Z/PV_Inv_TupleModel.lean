import R1Z.PV_Inv_CompressionFinite
import R0P.Copy
set_option autoImplicit false
namespace R1Z.PV_Inv_TupleModel
variable {K : Type} [Field K]

theorem model (lambda : K) (t : K × (Fin 16 → K)) :
    R0P.copyTupleValue lambda t=PV_Inv_Compression.loop lambda t.1 lambda (List.ofFn t.2) :=
  (PV_Inv_CompressionFinite.tagged_sixteen lambda t.1 t.2).symm

#print axioms model
end R1Z.PV_Inv_TupleModel
