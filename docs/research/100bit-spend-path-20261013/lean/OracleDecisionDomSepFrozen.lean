import BinSharedGrammarBridge
import R1PublicInitParse

/-! Literal refinement of the selected b2727acd3 R1 byte formats.
This does not assert that the full causal decoder rejects Merkle inputs:
public initialization and ordinary absorb recognition are different cases. -/
set_option autoImplicit false
noncomputable section
namespace AspisR1.OracleDecisionDomSepFrozen
open FS2.Duplex
open AspisV8R19.DuplexFrames AspisV8R19.SourceDuplexStep

/-- `multiproof::binary_parent`, at every one of the eighteen levels. -/
def node (cs : BinMerkle32Path.Children) : Bytes :=
  (0x12 : Byte) :: (List.ofFn (cs 0) ++ List.ofFn (cs 1))

/-- `state_only_private_merkle::private_leaf_hash_with_digest`. -/
def leaf (tag : Byte) (packed salt : Bytes) : Bytes :=
  (0x10 : Byte) :: tag :: (packed ++ salt)

/-- The 38-byte private semantic domain, independently written literally. -/
def initialDomain : Bytes :=
  [85, 78, 80, 82, 79, 86, 69, 68, 58, 82, 49, 58, 80, 82, 73,
   86, 65, 84, 69, 45, 83, 65, 76, 84, 69, 68, 58, 83, 69, 77,
   65, 78, 84, 73, 67, 58, 80, 51]

/-- The u32 little-endian length encoder is shared explicitly; source integer
and public-input serialization correspondence are separate obligations. -/
def initial (pub : Bytes) (root : State) : Bytes :=
  initialDomain ++ [0] ++ PublicInitFrame.lengthBytes pub.length ++ pub ++ bytes root

theorem shared_node_refines (cs : BinMerkle32Path.Children) :
    SharedBinaryRecordGrammar.nodeInput cs = node cs := rfl

theorem path_node_refines (cs : BinMerkle32Path.Children) :
    BinMerkle32Path.nodeInput cs = node cs :=
  BinSharedGrammarBridge.node_eq cs

theorem shared_leaf_refines (tag : Byte) (packed salt : Bytes) :
    SharedBinaryRecordGrammar.leafInput tag packed salt = leaf tag packed salt := rfl

theorem initial_refines (pub : Bytes) (root : State) :
    PublicInitFrame.frame pub root = initial pub root := rfl

theorem node_not_initial (cs : BinMerkle32Path.Children) (pub : Bytes) (root : State) :
    node cs ≠ initial pub root := by
  intro h
  have hh := congrArg List.head? h
  change some (18 : Byte) = some 85 at hh
  cases hh

theorem leaf_not_initial (tag : Byte) (packed salt pub : Bytes) (root : State) :
    leaf tag packed salt ≠ initial pub root := by
  intro h
  have hh := congrArg List.head? h
  change some (16 : Byte) = some 85 at hh
  cases hh

/-- Applies to canonical Merkle byte addresses without enumerating Addr L. -/
theorem node_init_parse_none {L : Nat} (cs : BinMerkle32Path.Children)
    (a : Addr L) (ha : a.toBytes = node cs) (pub : Bytes) :
    PublicInitParse.parse pub a = none := by
  cases hp : PublicInitParse.parse pub a with
  | none => rfl
  | some root =>
      have hs := (PublicInitParse.parse_sound pub a root hp).2
      have he : node cs = initial pub root := by simpa only [ha, initial, initialDomain,
        PublicInitFrame.domain] using hs
      exact False.elim (node_not_initial cs pub root he)

theorem leaf_init_parse_none {L : Nat} (tag : Byte) (packed salt : Bytes)
    (a : Addr L) (ha : a.toBytes = leaf tag packed salt) (pub : Bytes) :
    PublicInitParse.parse pub a = none := by
  cases hp : PublicInitParse.parse pub a with
  | none => rfl
  | some root =>
      have hs := (PublicInitParse.parse_sound pub a root hp).2
      have he : leaf tag packed salt = initial pub root := by simpa only [ha, initial,
        initialDomain, PublicInitFrame.domain] using hs
      exact False.elim (leaf_not_initial tag packed salt pub root he)

#print axioms shared_node_refines
#print axioms path_node_refines
#print axioms shared_leaf_refines
#print axioms initial_refines
#print axioms node_not_initial
#print axioms leaf_not_initial
#print axioms node_init_parse_none
#print axioms leaf_init_parse_none
end AspisR1.OracleDecisionDomSepFrozen
end
