import R1Z.PV_CB_ProducerTuple
import R1Z.PV_CurrentScaleInstall
set_option autoImplicit false
noncomputable section
namespace R1Z.PV_CB_ProducerContext
open Aeneas Aeneas.Std Result ProverRwFull PV_CB_ProducerLimb
variable [ExternalTypes]

theorem cell_congr (left right : ExternalFuns) (same : left.op73 = right.op73)
    (columns : Slice (alloc.vec.Vec U32)) (column row : Usize) (offset : U32) :
    @host_semantic.copy_cell _ left columns column row offset =
      @host_semantic.copy_cell _ right columns column row offset := by
  simp only [host_semantic.copy_cell,aspis_core.field.M31.add,same]

theorem limb_congr (left right : ExternalFuns) (same : left.op73 = right.op73)
    (zero : left.op55 = right.op55) (trace : Trace) (input : Limb) :
    @host_semantic.copy_tuple_limb _ left trace input =
      @host_semantic.copy_tuple_limb _ right trace input := by
  cases input with
  | Zero => simp only [host_semantic.copy_tuple_limb,aspis_core.field.M31.ZERO,zero]
  | Cell source offset =>
    cases source.bank <;>
      simp only [host_semantic.copy_tuple_limb,cell_congr left right same]

theorem tuple_congr (left right : ExternalFuns) (same : left.op73 = right.op73)
    (zero : left.op55 = right.op55) (trace : Trace) (input : PV_CB_ProducerTuple.Tuple) :
    @host_semantic.copy_tuple_values _ left trace input =
      @host_semantic.copy_tuple_values _ right trace input := by
  simp only [host_semantic.copy_tuple_values,limb_congr left right same zero]

#print axioms cell_congr
#print axioms limb_congr
#print axioms tuple_congr
end R1Z.PV_CB_ProducerContext
