import R1Z.BuilderPublicCanonical
import R1Z.BuilderFieldNormalization
import R1Z.BuilderProtocolInstance

/-! Assemble SourceIdentification from raw runtime records and admission.
No lane, helper, trace-validity or BuilderSoundOn field is assumed. The
runtime witness of this structure for the shipped compiler is still open. -/
set_option autoImplicit false
noncomputable section
namespace R1Z.BuilderRuntimeJoin
open R0P R0Z.WriterRefine R0Z.HonestValidity R0Z.ZkStatement
open R1J.SpendWitnessMap BuilderRecordCanonical
variable {K : Type} [Field K] [Fintype K] [DecidableEq K]
  [Algebra (ZMod AspisCircleGroupOrder.P) K] [CharP K 2147483647]

/-- One named remaining Rust join. Data is the compiler's raw word records
and full semantic public projection. Proofs must concern those same records.
The empty-root obligation is explicitly in publicCorr.empty; arbitrary-root
mapper equivalence cannot supply it. `admission` includes D50's sentinel.
Only WitnessOk's value/bit/sibling bounds are required, not canonical
key/owner/salt/pair words. The build handoff uses field-trace normalization,
so the two optional byte-roundtrip lemmas below are not assembly premises.
This record contains neither a source-identification certificate nor any of
the four soundness conclusions it is used to derive. -/
structure RustRuntimeJoin (source : HonestProver K) where
  publicInput : source.Instance → Public F
  witnessRecord : source.Instance → RustWitness
  publicRecord : source.Instance → RustPublic
  words : ∀ w, WitnessOk (witnessRecord w)
  publicCorr : ∀ w, PubCorr (publicRecord w) (mapPub (K := K) (publicInput w))
  admission : ∀ w, BuilderSpendRelation.RspendPlus
    (mapPub (K := K) (publicInput w))
    (BuilderCanonical.liftWitness (witness (witnessRecord w)))
  public_eq : ∀ w, source.public w = mapPub (publicInput w)
  raw_trace_eq : ∀ w, source.build w =
    BuilderRefinement.mergedTrace (witnessRecord w) (publicRecord w)
  transport_eq : source.transport = BuilderSource.π

variable {source : HonestProver K}

def toInstance (join : RustRuntimeJoin source) (w : source.Instance) :
    BuilderCanonical.Instance (K := K) :=
  ⟨(join.publicInput w, witness (join.witnessRecord w)), join.admission w⟩

theorem witness_record (join : RustRuntimeJoin source) (w : source.Instance)
    (hw : CanonicalWords (join.witnessRecord w)) :
    BuilderCanonical.rustWitness (toInstance join w).val.2 = join.witnessRecord w :=
  canonical_witness _ hw

theorem public_record (join : RustRuntimeJoin source) (w : source.Instance)
    (hp : PubCorr (join.publicRecord w) (join.publicInput w))
    (ha : (join.publicRecord w).asset.val < 2147483647) :
    BuilderCanonical.rustPublic (toInstance join w).val.1 = join.publicRecord w :=
  BuilderPublicCanonical.public_roundtrip _ _ hp ha

/-- Complete final assembly of the three original SourceIdentification
fields. The primitive runtime join is explicit, not constructed for Rust. -/
def sourceIdentification (join : RustRuntimeJoin source) :
    BuilderSource.SourceIdentification source (toInstance join) where
  public_eq := join.public_eq
  build_eq := by
    intro w
    rw [join.raw_trace_eq w, BuilderSource.build_map]
    exact BuilderFieldNormalization.trace_normalization _ _ _ (join.words w) (join.publicCorr w)
  transport_eq := join.transport_eq

theorem builder_refinement_D46_D51 {CommitHandle : Type}
    (hcard : 4096 < Fintype.card K) (Fbase : Subfield K)
    (B : PackBasis Fbase) (x : Statement K CommitHandle)
    (join : RustRuntimeJoin source) : BuilderSoundOn source B x :=
  BuilderSource.builder_refinement_D46_D51 hcard Fbase B x source
    (toInstance join) (sourceIdentification join)

#print axioms witness_record
#print axioms public_record
#print axioms sourceIdentification
#print axioms builder_refinement_D46_D51
end R1Z.BuilderRuntimeJoin
