import R1Z.ProverCommitReferenceReads
import R1Z.ProverCommitSourceDecoder

/-! A fixed operational decoder from the extracted scalar caller. Unlike
representativeDecoder this executes the extracted next-word and sixteen-try
loop. The model builder balances the raw arrays after decoding. Identifying
this raw producer with the complete shipped producer is a separate obligation. -/
set_option autoImplicit false
noncomputable section
namespace R1Z.ProverCommitOwnedDecoder
open Aeneas Aeneas.Std Result
open R0Z.FsStatement R0Z.JointView
open R1Z.ProverCommitStepLoop (State Hash)
open R1Z.ProverCommitStreamSource (Bytes32 blockSlices)
open R1Z.ProverCommitSourceDecoder
open R1Z.ProverCommitWordCarrier (sourceBase)
open R1Z.ProverCommitTapeCompletion
attribute [local instance] Classical.propDecidable

/-- Decode the little-endian counter frame; no oracle or hash is evaluated. -/
def littleEndian : List U8 → Nat
  | [] => 0
  | b :: bs => b.val + 256 * littleEndian bs

/-- The finite oracle backend. Requests outside the allocated block stream
retain an operational failure instead of supplying fresh or padded words. -/
def blockHash {n : Nat} (answers : Fin n → OracleAnswer) : Hash := fun frame =>
  let counter := littleEndian (match frame.val[2]? with | none => [] | some bytes => bytes.val)
  if hi : counter < n then
    ok (Aeneas.Std.Array.make 32#usize
      (List.ofFn (fun i : Fin 32 => UScalar.mk (BitVec.ofNat 8 ((answers ⟨counter, hi⟩ i).toNat)))))
  else fail .panic

/-- Both shipped expanders begin with an empty cache and counter zero.
The seed value is immaterial to a backend indexed by its counter frame. -/
def initial : State :=
  ⟨Aeneas.Std.Array.repeat 32#usize 0#u8, 0#u64,
    Aeneas.Std.Array.repeat 32#usize 0#u8, 8#usize⟩

/-- Preserve the actual error path; only successful raw scalar arrays survive. -/
def samples (hash : Hash) (domain : Slice U8) (count : Nat) : Option (List U32) :=
  match R1Z.ProverCommitFourSteps.collect
    (AspisR1ProverStep8.prover_commit_reference.limb_caller hash domain) count initial with
  | .ok (.Ok values, _) => some values
  | _ => none

variable {K : Type} [Field K] [Algebra (ZMod AspisCircleGroupOrder.P) K]
local notation "F" => sourceBase (K := K)

/-- Total value conversion; the extracted sampler only returns canonical M31s. -/
def fieldValue (v : U32) : F :=
  R1Z.ProverCommitWordCarrier.baseEquiv
    ⟨v.val % AspisCircleGroupOrder.P, Nat.mod_lt _ (by decide)⟩

def rawArrays (hash₁ hash₂ : Hash) : Option ((Fin L₁ → F) × (Fin L₂ → F)) := do
  let a ← samples hash₁ AspisR1ProverStreams.state_only_hiding.MASK_EXPAND_DOMAIN L₁
  let b ← samples hash₂ AspisR1ProverStreams.state_only_entropy.PROFILE21_SOURCE_EXPAND_DOMAIN L₂
  pure ((fun i => fieldValue (a[i.val]?.getD 0#u32)),
    (fun i => fieldValue (b[i.val]?.getD 0#u32)))

/-- Raw coordinates are retained for the protocol's existing balancing builder.
This is a concrete executable-reference composition, not an assumed equation
with quotientDecoder. -/
def decodeWith (hash₁ hash₂ : Hash) : Option (Tape K F) :=
  (rawArrays hash₁ hash₂).map (fun arrays =>
    R1Z.ProverCommitSourceCarrier.toTape
      (R1Z.ProverCommitSourceCarrier.fromQuotient (arrayCarrierEquiv arrays)))

def decoder (a : Fin E₁ → OracleAnswer) (b : Fin E₂ → OracleAnswer) :
    Option (Tape K F) := decodeWith (blockHash a) (blockHash b)

/-- Universal callback support of the composed reference, with no successful
execution assumption and with failure/divergence preserved by collect. -/
theorem samples_support (left right : Hash) (domain : Slice U8)
    (same : ∀ (seed : Bytes32) (counter : U64),
      left (blockSlices domain seed counter) = right (blockSlices domain seed counter))
    (count : Nat) : samples left domain count = samples right domain count := by
  unfold samples
  rw [R1Z.ProverCommitReferenceReads.all_calls_support left right domain same]

theorem decode_support (left₁ right₁ left₂ right₂ : Hash)
    (same₁ : ∀ (seed : Bytes32) (counter : U64),
      left₁ (blockSlices AspisR1ProverStreams.state_only_hiding.MASK_EXPAND_DOMAIN seed counter) =
      right₁ (blockSlices AspisR1ProverStreams.state_only_hiding.MASK_EXPAND_DOMAIN seed counter))
    (same₂ : ∀ (seed : Bytes32) (counter : U64),
      left₂ (blockSlices AspisR1ProverStreams.state_only_entropy.PROFILE21_SOURCE_EXPAND_DOMAIN seed counter) =
      right₂ (blockSlices AspisR1ProverStreams.state_only_entropy.PROFILE21_SOURCE_EXPAND_DOMAIN seed counter)) :
    decodeWith (K := K) left₁ left₂ = decodeWith right₁ right₂ := by
  simp only [decodeWith, rawArrays, samples_support left₁ right₁ _ same₁,
    samples_support left₂ right₂ _ same₂]

/-- Projection exposes the exact remaining scalar/cursor refinement goal. -/
theorem quotient_decodeWith (hash₁ hash₂ : Hash) :
    (decodeWith (K := K) hash₁ hash₂).map project =
      (rawArrays hash₁ hash₂).map arrayCarrierEquiv := by
  cases h : rawArrays (K := K) hash₁ hash₂ with
  | none => simp only [decodeWith, h, Option.map_none]
  | some arrays =>
    simp only [decodeWith, h, Option.map_some,
      R1Z.ProverCommitSourceCarrier.to_from]

#print axioms samples_support
#print axioms decode_support
#print axioms quotient_decodeWith
end R1Z.ProverCommitOwnedDecoder
