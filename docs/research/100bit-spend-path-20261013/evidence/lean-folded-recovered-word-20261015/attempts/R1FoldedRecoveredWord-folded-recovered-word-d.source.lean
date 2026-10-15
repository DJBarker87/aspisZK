import R1FoldedLeafCodec
import R1MerkleIndexGeometry
import R1LaterTableStability

/-! Total WideExact word formed from strict folded-leaf recovery. This is a
representation bridge over caller-supplied or table-recovered leaves only. -/
set_option autoImplicit false

namespace AspisR1.FoldedRecoveredWord

open AspisR1.FoldedLeafCodec
open AspisR1.MerkleIndexGeometry
open AspisR1.CanonicalTableRecovery
open AspisV8R19.SourceDuplexStep AspisV8R19.DuplexFrames
open FS FS2.Duplex

abbrev Wide := AspisR1.FoldedLeafCodec.Wide
abbrev Folded := AspisR1.FoldedLeafCodec.Folded

variable {M Cv : Type} {L : Nat}

/-- Original query position modulo the four folded words in a Merkle leaf. -/
def foldedSlot (i : Fin 262144) : Fin 4 :=
  ⟨i.val % 4, Nat.mod_lt _ (by decide)⟩

/-- The canonical zero value used when a folded leaf is absent or malformed. -/
def zeroFolded : Folded := fun _ => 0

/-- Project one strict folded-leaf decode to the word at the query slot. -/
def wordOfPacked (packed : Option (List Byte)) (i : Fin 262144) : Wide :=
  ((packed.bind decodeFolded).getD zeroFolded) (foldedSlot i)

/-- A successful strict decode selects exactly the requested folded slot. -/
theorem wordOfPacked_success (packed : Option (List Byte)) (bytes : List Byte)
    (xs : Folded) (i : Fin 262144)
    (hpacked : packed = some bytes) (hdecode : decodeFolded bytes = some xs) :
    wordOfPacked packed i = xs (foldedSlot i) := by
  simp [wordOfPacked, hpacked, hdecode]

/-- Recovered packed folded-leaf bytes at the six-level path for a leaf. -/
def packedAt (tr : List (Addr L × State)) (root : State)
    (leaf : Fin 65536) : Option (List Byte) :=
  (recoverAt 0x72 128 tr (MerkleIndexGeometry.slots 6 leaf.val) root).map Prod.fst

/-- Total WideExact word induced by packed folded leaves, with invalid or
missing leaves mapped to four zero values. -/
def wordAt (tr : List (Addr L × State)) (root : State)
    (i : Fin 262144) : Wide :=
  wordOfPacked (packedAt tr root (foldedIndex i)) i

theorem foldedIndex_slot_decompose (i : Fin 262144) :
    i.val = 4 * (foldedIndex i).val + (foldedSlot i).val := by
  simpa [foldedSlot] using MerkleIndexGeometry.foldedIndex_decompose i

/-- Transfer the total folded word from the represented table immediately
before its first folded-frame read to the consistent full trace. All event,
read, table, and path premises are exactly those of the existing recovery
stability theorem. -/
theorem folded_word_table_of_read (p : Params M Cv L) (Qtot : Nat)
    (H : Addr L → State) (tr represented : List (Addr L × State))
    (state : State) (tail : Bytes) (htail : tail.length = 224)
    (hframe : 294 ≤ L) (root : State)
    (hsize : 162 ≤ L) (hnode : 257 ≤ L)
    (hcons : ∀ q ∈ tr, q.2 = H q.1)
    (hrepresented : ∀ q ∈ represented, q.2 = H q.1)
    (hread : Read tr (CommitmentRootFrames.foldedAddr state root tail htail hframe))
    (hQ : firstReads emptyTable tr ≤ Qtot)
    (hnoColl : ¬ hitsBad (badColl p Qtot) emptyTable tr)
    (hnoChild : ¬ hitsBad (ParsedTargetsCollision.bad MerkleChildTargets.pred Qtot)
      emptyTable tr)
    (hnoRoot : ¬ hitsBad (ParsedTargetsCollision.bad CommitmentRootTargets.pred Qtot)
      emptyTable tr)
    (htable : TraceTable.replay (emptyTable : Table (Addr L) State) represented =
      tableBefore emptyTable tr
        (CommitmentRootFrames.foldedAddr state root tail htail hframe)) :
    wordAt represented root = wordAt tr root := by
  have hrec := LaterTableStability.folded_table_word_of_read p Qtot H tr represented
    state tail htail hframe root hsize hnode hcons hrepresented hread hQ hnoColl
    hnoChild hnoRoot htable
  funext i
  unfold wordAt packedAt
  exact congrArg (fun recovered : Option (List Byte × List Byte) =>
    wordOfPacked (recovered.map Prod.fst) i)
    (congrFun hrec (MerkleIndexGeometry.slots 6 (foldedIndex i).val))

#print axioms wordOfPacked_success
#print axioms foldedIndex_slot_decompose
#print axioms folded_word_table_of_read

end AspisR1.FoldedRecoveredWord
