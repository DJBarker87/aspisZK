import R1PublicSourceRawSuccess

/-! Explicit remaining current-source boundary.
`sourceReturns` must describe a successful evaluation of the pinned current
Rust `r0::Public::public_bytes`, with its byte conversion fixed; `project`
must copy the actual source coordinates into PublicSourceRaw.Public.
Neither that semantics nor its refinement proof is supplied here.

The contracts below are propositions passed as theorem hypotheses, not
axioms or evidence that the current Rust serializer has been extracted.
They only transport successful results and make no equivalence claim about
panic/allocation/rejection traces, Pool/ASF8 parsing, or omitted metadata. -/
set_option autoImplicit false
namespace AspisR1.PublicSourceBoundary

open PublicSourceRaw

variable {Source : Type}

/-- The unresolved source theorem: actual successful bytes equal this
fixed raw-u32 model's bytes. Both the source semantics and coordinate
projection must be tied to the current Rust, not chosen to fit a result. -/
def SourceSerializerRefines (sourceReturns : Source → Bytes → Prop)
    (project : Source → Public) : Prop :=
  ∀ source bytes, sourceReturns source bytes → serialize (project source) = some bytes

/-- Only the amount consequence of actual successful source validation.
This is not a definition of validation or a proof of any other payment guard. -/
def SourceValidationAmountGuard (validated : Source → Prop)
    (project : Source → Public) : Prop :=
  ∀ source, validated source → PaymentAmountGuard (project source)

theorem mapped_of_source_success (sourceReturns : Source → Bytes → Prop)
    (project : Source → Public)
    (hrefine : SourceSerializerRefines sourceReturns project)
    (source : Source) (bytes : Bytes) (hsource : sourceReturns source bytes) :
    ∃ wire, toWire (project source) = some wire ∧
      PublicByteCodec.encode (SemanticPublicWire.toPublic wire) = some bytes := by
  exact PublicSourceRawSuccess.toWire_of_serialize (project source) bytes
    (hrefine source bytes hsource)

theorem encode_of_source_success (sourceReturns : Source → Bytes → Prop)
    (project : Source → Public)
    (hrefine : SourceSerializerRefines sourceReturns project)
    (source : Source) (bytes : Bytes) (hsource : sourceReturns source bytes)
    (pub : R0P.Public M31) (hrel : PublicSourceRawMap.RustPublicRel (project source) pub) :
    PublicByteCodec.encode pub = some bytes := by
  exact PublicSourceRawMap.encode_of_serialize (project source) pub bytes
    (hrefine source bytes hsource) hrel

/-- Syntactic decoding does not require withdrawal nonzero. -/
theorem parseRaw_of_source_success (sourceReturns : Source → Bytes → Prop)
    (project : Source → Public)
    (hrefine : SourceSerializerRefines sourceReturns project)
    (source : Source) (bytes : Bytes) (hsource : sourceReturns source bytes)
    (pub : R0P.Public M31) (hrel : PublicSourceRawMap.RustPublicRel (project source) pub) :
    PublicByteCodec.parseRaw bytes = some pub := by
  exact (PublicByteCodec.parseRaw_eq_some_iff bytes pub).mpr
    (encode_of_source_success sourceReturns project hrefine source bytes hsource pub hrel)

theorem decode_of_source_success (sourceReturns : Source → Bytes → Prop)
    (project : Source → Public)
    (hrefine : SourceSerializerRefines sourceReturns project)
    (source : Source) (bytes : Bytes) (hsource : sourceReturns source bytes)
    (pub : R0P.Public M31) (hrel : PublicSourceRawMap.RustPublicRel (project source) pub)
    (hnonzero : NonzeroWithdrawal (project source)) :
    PublicByteCodec.decode bytes = some pub := by
  exact PublicSourceRawMap.decode_of_serialize (project source) pub bytes
    (hrefine source bytes hsource) hrel hnonzero

theorem decoded_of_source_success (sourceReturns : Source → Bytes → Prop)
    (project : Source → Public)
    (hrefine : SourceSerializerRefines sourceReturns project)
    (source : Source) (bytes : Bytes) (hsource : sourceReturns source bytes)
    (hnonzero : NonzeroWithdrawal (project source)) :
    ∃ wire, toWire (project source) = some wire ∧
      PublicByteCodec.decode bytes = some (SemanticPublicWire.toPublic wire) := by
  exact PublicSourceRawSuccess.decode_of_serialize (project source) bytes
    (hrefine source bytes hsource) hnonzero

theorem decoded_of_validated_source_success (sourceReturns : Source → Bytes → Prop)
    (validated : Source → Prop) (project : Source → Public)
    (hrefine : SourceSerializerRefines sourceReturns project)
    (hguard : SourceValidationAmountGuard validated project)
    (source : Source) (bytes : Bytes) (hsource : sourceReturns source bytes)
    (hvalidated : validated source) :
    ∃ wire, toWire (project source) = some wire ∧
      PublicByteCodec.decode bytes = some (SemanticPublicWire.toPublic wire) := by
  exact decoded_of_source_success sourceReturns project hrefine source bytes hsource
    (PublicSourceRawMap.nonzero_of_payment_guard (project source)
      (hguard source hvalidated))

#print axioms mapped_of_source_success
#print axioms encode_of_source_success
#print axioms parseRaw_of_source_success
#print axioms decode_of_source_success
#print axioms decoded_of_source_success
#print axioms decoded_of_validated_source_success

end AspisR1.PublicSourceBoundary
