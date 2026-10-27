import R1Z.PV_CB_ProducerLocalLimb
import R1Z.PV_CB_ProducerTuple
set_option autoImplicit false
namespace R1Z.PV_CB_ProducerReadRestriction
open Aeneas Aeneas.Std Result ProverRwFull PV_CB_ProducerLimb
variable [ExternalTypes]

theorem cell (columns : Slice PV_CB_ProducerCell.V) (global : PV_CB_ProducerCell.Reads columns)
    (column row : Usize) : PV_CB_ProducerLocalCell.ReadsAt columns column row :=
  fun vector hv word hw => global column vector hv row word hw

theorem limb (trace : Trace) (global : TraceReads trace) (input : Limb) :
    PV_CB_ProducerLocalLimb.Reads trace input := by
  cases input with
  | Zero => trivial
  | Cell source offset =>
    cases hb : source.bank with
    | Stable =>
      simpa only [PV_CB_ProducerLocalLimb.Reads,hb] using
        (cell _ global.1 (UScalar.cast .Usize source.cell.column) (UScalar.cast .Usize source.cell.row))
    | Late =>
      simpa only [PV_CB_ProducerLocalLimb.Reads,hb] using
        (cell _ global.2 (UScalar.cast .Usize source.cell.column) (UScalar.cast .Usize source.cell.row))

theorem tuple (trace : Trace) (global : TraceReads trace) (input : PV_CB_ProducerTuple.Tuple) :
    PV_CB_CanonicalArrays.Valid (PV_CB_ProducerLocalLimb.Reads trace) input.limbs :=
  fun value _ => limb trace global value
#print axioms cell
#print axioms limb
#print axioms tuple
end R1Z.PV_CB_ProducerReadRestriction
