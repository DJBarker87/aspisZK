import R1Z.PV_Inv_CompressionFinite
import R1Z.PV_Inv_NativeCompress
import R0P.Copy
set_option autoImplicit false
noncomputable section
namespace R1Z.PV_Inv_WordTuple
open Aeneas Aeneas.Std
open AspisR1.ExtractedCurrentQM31Exact (QM31Exact)

def tuple (tag : U32) (limbs : Fin 16 → U32) : QM31Exact × (Fin 16 → QM31Exact) :=
  (ProverCommitScalar48.embed tag, fun i => ProverCommitScalar48.embed (limbs i))

theorem model (lambda : QM31Exact) (tag : U32) (limbs : Fin 16 → U32) :
    R0P.copyTupleValue (K := QM31Exact) lambda (tuple tag limbs) =
      PV_Inv_Compression.loop lambda (ProverCommitScalar48.embed tag) lambda
        (List.ofFn (fun i : Fin 16 => ProverCommitScalar48.embed (limbs i))) := by
  exact (PV_Inv_CompressionFinite.tagged_sixteen lambda (ProverCommitScalar48.embed tag)
    (fun i => ProverCommitScalar48.embed (limbs i))).symm

#print axioms model
end R1Z.PV_Inv_WordTuple
