import R1Z.BuilderPrimitiveArguments
import R1Z.BuilderFieldNormalization

/-! Construct raw extracted bank records from canonical mathematical records.
This is an inhabitance witness, not an assertion about the opaque records
callee in the forest entry point. The U64 bound stays explicit. -/
set_option autoImplicit false
noncomputable section
namespace R1Z.PV_Src_Records
open Aeneas Aeneas.Std Result R0Z.WriterRefine R1J.SpendWitnessMap
open AspisBuilderGlueSource.pool_v1.pair_forest_copy_builder

def bankWitness (w : RustWitness) : RW where
  input_value := w.inputValue
  output_value := w.outputValue
  change_value := w.changeValue
  sk := w.sk
  salt := w.salt
  bits := w.bits
  sibs := w.sibs
  pair_first := w.pairFirst
  pair_occupied := w.pairOccupied
  pair_second := w.pairSecond
  pair_inverse := w.pairInverse
  recipient_owner := w.recipientOwner
  recipient_salt := w.recipientSalt
  change_owner := w.changeOwner
  change_salt := w.changeSalt

def bankPublic (p : RustPublic) (bound : p.nextPairIndex < 2^64) : RP where
  transfer := match p.variant with | .privateTransfer => true | .withdrawal => false
  asset := p.asset
  next_pair_index := UScalar.ofNatCore p.nextPairIndex bound
  frontier := p.frontier
  empty := p.empty

theorem witness_roundtrip (w : RustWitness) :
    BuilderPrimitiveArguments.wordWitness (bankWitness w) = w := by cases w; rfl

theorem public_roundtrip (p : RustPublic) (bound : p.nextPairIndex < 2^64) :
    BuilderPrimitiveArguments.wordPublic (bankPublic p bound) = p := by
  cases p with
  | mk v a n f e => cases v <;> rfl

theorem decoded_witness (w : AspisR1.SpendRelation.Wspend) :
    BuilderRecordCanonical.witness (BuilderCanonical.rustWitness w) = w := by
  unfold BuilderRecordCanonical.witness BuilderCanonical.rustWitness
  rw [toModel_toRust]
  simp only [mapW,ι_apply,ZMod.natCast_zmod_val]
  cases w
  rfl

#print axioms witness_roundtrip
#print axioms public_roundtrip
#print axioms decoded_witness
end R1Z.PV_Src_Records
