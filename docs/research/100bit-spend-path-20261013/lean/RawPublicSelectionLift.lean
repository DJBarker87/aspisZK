import RawBoundedTrace
import RawAdaptiveLiteralDecoder

/-! Lift a table-only bounded public selector to unrestricted byte queries.
Noncanonical inputs are not decoder candidates; oracle queries themselves
remain unrestricted. The exact chronological table is preserved. -/
set_option autoImplicit false
noncomputable section
namespace AspisR1.RawPublicSelectionLift
open FS FS2 FS2.Duplex AspisV8PairedCommitment
open AspisV8R19.DuplexFrames AspisV8R19.SourceDuplexStep
open CanonicalAddressEmbedding

def select (L : Nat) (bounded : Addr L → Table (Addr L) State → Option (UnifiedSampler.Public L))
    (a : Bytes) (T : Table Bytes State) : Option (UnifiedSampler.Public L) :=
  (CanonicalRawTrace.decode L a).bind fun ac => bounded ac.val (RawBoundedTrace.table L T)

theorem of_canonical (L : Nat)
    (bounded : Addr L → Table (Addr L) State → Option (UnifiedSampler.Public L))
    (a : AddrC L) (T : Table Bytes State) :
    select L bounded (toBytes a) T = bounded a.val (RawBoundedTrace.table L T) := by
  have hc := (CanonicalRawTrace.embedding L).decode_embed a
  change CanonicalRawTrace.decode L (toBytes a) = some a at hc
  simp only [select,hc,Option.bind_some]

theorem at_current_table (L : Nat)
    (bounded : Addr L → Table (Addr L) State → Option (UnifiedSampler.Public L))
    (a : AddrC L) (tr : List (Bytes × State)) :
    select L bounded (toBytes a) (tableBefore emptyTable tr (toBytes a)) =
      bounded a.val (tableBefore emptyTable (RawBoundedTrace.trace L tr) a.val) := by
  rw [of_canonical]
  have ht := RawBoundedTrace.tableBefore_trace L emptyTable tr a
  rw [RawBoundedTrace.table_empty] at ht
  exact congrArg (bounded a.val) ht.symm

theorem density (protocolDecoder : LiteralByteProtocol.Decoder)
    (bounded : Addr SelectedTranscriptParams.L → Table (Addr SelectedTranscriptParams.L) State →
      Option LiteralTranscript.Public) (words : RawLiteralDecoderDensity.WordChoice) :
    R0C.V3.ChainDensity3 (LiteralByteProtocol.protocol protocolDecoder) LiteralByteProtocol.rows
      (RawAdaptiveLiteralDecoder.decode (select SelectedTranscriptParams.L bounded) words) :=
  RawAdaptiveLiteralDecoder.density protocolDecoder (select SelectedTranscriptParams.L bounded) words

#print axioms at_current_table
#print axioms density
end AspisR1.RawPublicSelectionLift
end
