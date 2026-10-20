import LiteralTableWordChoice
import RawByteTableWordsBin

set_option autoImplicit false
noncomputable section
namespace AspisR1.LiteralTableWordChoiceBin
open FS FS2 AspisV8PairedCommitment AspisV8R19.DuplexFrames AspisV8R19.SourceDuplexStep
open LiteralDecoderEnrichment CanonicalCutEnrichedTranscript LiteralTableWordChoice

/-- The same causal root selection with strict binary table recovery. -/
def choose (_ : Bytes) (T : Table Bytes State) (P : ErasedPrefix) (m : ErasedMessage) : Words :=
  RawByteTableWordsBin.words T T T (c1Root P m) (c2Root P m) (finalRoot P m)

#print axioms choose
end AspisR1.LiteralTableWordChoiceBin
end
