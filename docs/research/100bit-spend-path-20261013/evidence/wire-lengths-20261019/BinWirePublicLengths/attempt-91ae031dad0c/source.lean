import BinGrammar
import R1SemanticPublicByteBinding

/-! The semantic public wire has two lengths, not one. The checkpoint's
ASF8 bytes and ASQ8 request are different encodings (see the design note). -/
set_option autoImplicit false
namespace AspisR1.BinWirePublicLengths
open SemanticPublicWire

theorem parsed_lengths (bs : List Byte) (pub : R0P.Public M31)
    (h : parsePublic bs = some pub) : bs.length = 1455 ∨ bs.length = 1427 := by
  rw [SemanticPublicByteBinding.parsed_length bs pub h]
  split <;> simp

theorem parsed_ne_node (bs : List Byte) (pub : R0P.Public M31)
    (h : parsePublic bs = some pub) (cs : BinMerkle32Path.Children) :
    BinMerkle32Path.nodeInput cs ≠ bs := by
  apply BinGrammar.node_ne_length
  have hl := parsed_lengths bs pub h
  omega

/-- Counterexample to a variant-independent fixed semantic-public length. -/
theorem variants_differ (c : Common) (recipient : Digest) (amount : M31) :
    (encode (.transfer c recipient)).length ≠ (encode (.withdrawal c amount)).length := by
  rw [SemanticPublicWireRoundTrip.encode_length, SemanticPublicWireRoundTrip.encode_length]
  change (1455 : Nat) ≠ 1427
  omega

/-- Applies to the fixed ASF8 statement (1880) or ASQ8 request (320).
Their Rust serializer/refinement is not supplied by this arithmetic fact. -/
theorem fixed_public_ne_node (bs : List BinMerkle32Path.Byte)
    (h : bs.length = 1880 ∨ bs.length = 320) (cs : BinMerkle32Path.Children) :
    BinMerkle32Path.nodeInput cs ≠ bs := by
  apply BinGrammar.node_ne_length
  omega

#print axioms parsed_lengths
#print axioms parsed_ne_node
#print axioms variants_differ
#print axioms fixed_public_ne_node
end AspisR1.BinWirePublicLengths
