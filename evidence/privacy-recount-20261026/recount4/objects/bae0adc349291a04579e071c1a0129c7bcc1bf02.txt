import R1Z.BuilderRecordsExtracted
import R1Z.BuilderFieldNormalization

/-! The nominal type adapter from the extracted owned-reference records to
all fields of the R1Z word-level builder. No record field is reconstructed
from another or dropped. Public next_pair_index is interpreted as its U64
value, and the source transfer flag selects the semantic variant. -/
set_option autoImplicit false
noncomputable section
namespace R1Z.BuilderExtractedRecords
open R0P R0Z.WriterRefine R1J.SpendWitnessMap
abbrev RW := AspisBuilderRecordsReference.pool_v1.pair_forest_copy_builder.RW
abbrev RP := AspisBuilderRecordsReference.pool_v1.pair_forest_copy_builder.RP

def rawWitness (w : RW) : RustWitness where
  inputValue := w.input_value
  outputValue := w.output_value
  changeValue := w.change_value
  sk := w.sk
  salt := w.salt
  bits := w.bits
  sibs := w.sibs
  pairFirst := w.pair_first
  pairOccupied := w.pair_occupied
  pairSecond := w.pair_second
  pairInverse := w.pair_inverse
  recipientOwner := w.recipient_owner
  recipientSalt := w.recipient_salt
  changeOwner := w.change_owner
  changeSalt := w.change_salt

def rawPublic (p : RP) : RustPublic where
  variant := if p.transfer then .privateTransfer else .withdrawal
  asset := p.asset
  nextPairIndex := p.next_pair_index.val
  frontier := p.frontier
  empty := p.empty

variable {K : Type} [Field K] [Fintype K] [DecidableEq K]
  [Algebra (ZMod AspisCircleGroupOrder.P) K] [CharP K 2147483647]

/-- The full extracted record types feed the canonical builder without any
canonicality hypothesis on owner/key/salt/pair words. Empty roots remain in
the explicit PubCorr premise until the runtime helper certificate is joined.
This holds for every returned record pair, not only a selected input fixture. -/
theorem reference_trace (w : RW) (p : RP) (pub : Public F)
    (hw : WitnessOk (rawWitness w))
    (hp : PubCorr (rawPublic p) (mapPub (K := K) pub)) :
    BuilderRefinement.mergedTrace (K := K) (rawWitness w) (rawPublic p) =
      BuilderRefinement.mergedTrace
        (BuilderCanonical.rustWitness (BuilderRecordCanonical.witness (rawWitness w)))
        (BuilderCanonical.rustPublic pub) :=
  BuilderFieldNormalization.trace_normalization _ _ _ hw hp

#print axioms reference_trace
end R1Z.BuilderExtractedRecords
