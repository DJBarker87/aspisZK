import R1Z.BuilderForestAdmissionPort
import R1Z.BuilderPrimitiveArguments
import R1Z.PV_Src_Forest_PrimitiveArguments

/-! Preserve every raw record field across the two extracted nominal record
carriers. These are data adapters, not an implementation of the opaque
forest Records callback. They do not assert that a callback returns them. -/
set_option autoImplicit false
namespace R1Z.PV_Src_ForestRecords
open Aeneas Aeneas.Std Result
abbrev FW := BuilderForestAdmissionPort.pool_v1.pair_forest_copy_builder.RW
abbrev FP := BuilderForestAdmissionPort.pool_v1.pair_forest_copy_builder.RP
abbrev BW := AspisBuilderGlueSource.pool_v1.pair_forest_copy_builder.RW
abbrev BP := AspisBuilderGlueSource.pool_v1.pair_forest_copy_builder.RP

def witness (w : FW) : BW where
  input_value := w.input_value
  output_value := w.output_value
  change_value := w.change_value
  sk := w.sk
  salt := w.salt
  bits := w.bits
  sibs := w.sibs
  pair_first := w.pair_first
  pair_occupied := w.pair_occupied
  pair_second := w.pair_second
  pair_inverse := w.pair_inverse
  recipient_owner := w.recipient_owner
  recipient_salt := w.recipient_salt
  change_owner := w.change_owner
  change_salt := w.change_salt

def publicRecord (p : FP) : BP where
  transfer := p.transfer
  asset := p.asset
  next_pair_index := p.next_pair_index
  frontier := p.frontier
  empty := p.empty

def restoreWitness (w : BW) : FW where
  input_value := w.input_value
  output_value := w.output_value
  change_value := w.change_value
  sk := w.sk
  salt := w.salt
  bits := w.bits
  sibs := w.sibs
  pair_first := w.pair_first
  pair_occupied := w.pair_occupied
  pair_second := w.pair_second
  pair_inverse := w.pair_inverse
  recipient_owner := w.recipient_owner
  recipient_salt := w.recipient_salt
  change_owner := w.change_owner
  change_salt := w.change_salt

def restorePublic (p : BP) : FP where
  transfer := p.transfer
  asset := p.asset
  next_pair_index := p.next_pair_index
  frontier := p.frontier
  empty := p.empty

theorem witness_roundtrip (w : FW) : restoreWitness (witness w) = w := by cases w; rfl
theorem witness_roundtrip_reverse (w : BW) : witness (restoreWitness w) = w := by cases w; rfl
theorem public_roundtrip (p : FP) : restorePublic (publicRecord p) = p := by cases p; rfl
theorem public_roundtrip_reverse (p : BP) : publicRecord (restorePublic p) = p := by cases p; rfl

theorem word_witness (w : BW) :
    PV_Src_Forest_PrimitiveArguments.wordWitness (restoreWitness w) =
      BuilderPrimitiveArguments.wordWitness w := rfl

theorem word_public (p : BP) :
    PV_Src_Forest_PrimitiveArguments.wordPublic (restorePublic p) =
      BuilderPrimitiveArguments.wordPublic p := rfl

#print axioms word_witness
#print axioms word_public
#print axioms witness_roundtrip
#print axioms witness_roundtrip_reverse
#print axioms public_roundtrip
#print axioms public_roundtrip_reverse
end R1Z.PV_Src_ForestRecords
