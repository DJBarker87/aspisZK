import R1Z.ProverRw18CopyPolynomial
import R1Z.ProverCommitValueRange47
set_option autoImplicit false
noncomputable section
namespace R1Z.ProverRw18CopyWide
open Aeneas Aeneas.Std ProverRw18FieldMeaning
open scoped BigOperators
abbrev W := AspisWideTower.WideExact

def tuple (tag : U32) (values : Fin 16 → U32) : W × (Fin 16 → W) :=
  ((tag.val : W),fun i => ((values i).val : W))

theorem value (tag : U32) (values : Fin 16 → U32) (lambda : K) :
    algebraMap K W (ProverRw18FieldReference.value tag (List.ofFn values) lambda)=
      (R0P.compressPoly (tuple tag values)).eval (algebraMap K W lambda) := by
  rw [ProverRw18CopyPolynomial.value,R0P.compressPoly_eval,R0P.compressPoly_eval]
  simp only [ProverRw18CopyPolynomial.tuple,tuple,R0P.copy_powers_eq,
    map_add,map_sum,map_mul,map_pow,map_natCast]

#print axioms value
end R1Z.ProverRw18CopyWide
