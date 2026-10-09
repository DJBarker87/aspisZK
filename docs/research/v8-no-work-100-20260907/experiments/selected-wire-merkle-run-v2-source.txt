import SelectedWireBytes
import RustShapedMinimalMultiproof
import SelectedMultiproofOpeningEquality

/-! The selected Wire parser and Rust-shaped Merkle functional verifier share
the same body-derived roots, records and frontier halves.  Functional success
therefore constructs the typed `Accepted` object consumed by the opening
binding theorem; it is not supplied separately.

The only lower source boundary retained is equivalence of this total
functional verifier with the compiled Rust mutable-Vec implementation.
-/
set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 250
set_option maxHeartbeats 250000

namespace AspisV8.SelectedWireMerkleRun
open AspisPool.V7MerkleQueryGrammar
open AspisPool.V7MerkleQueryExtractor
open AspisV8.SelectedWireBytes AspisV8.MinimalMultiproofPaths
open AspisV8.RustShapedMinimalMultiproof
open AspisV8.SelectedMultiproofOpeningEquality

abbrev Byte := AspisPool.V7MerkleQueryGrammar.Byte

def wireRoots (wire : Wire) : Digests := wire.roots

def wireRecords (wire : Wire) : Fin 22 → Record :=
  fun i => recordOfBytes (wire.record i)

/-- Success is one result over the parsed Wire's literal fields; roots,
records and frontiers cannot be replaced by independent theorem inputs. -/
structure SuccessfulMerkleRun (view : RawHashInput → Digest208)
    (queries : Fin 22 → Position) (body : List Byte) where
  wire : Wire
  parsed : SelectedWireBytes.parse body = some wire
  trace : OrderedRawQueryLog
  verified : RustShapedMinimalMultiproof.verify view (wireRoots wire) 18
    (sortedEntries view queries (wireRecords wire))
    (wire.frontiers 0) (wire.frontiers 1) = some trace

theorem successful_constructs_accepted
    (view : RawHashInput → Digest208) (queries : Fin 22 → Position)
    (body : List Byte) (success : SuccessfulMerkleRun view queries body) :
    Accepted view (wireRoots success.wire) queries (wireRecords success.wire)
      (RustShapedMinimalMultiproof.frontierPairs
        (success.wire.frontiers 0) (success.wire.frontiers 1)) success.trace :=
  verify_selected_accepted view (wireRoots success.wire) queries
    (wireRecords success.wire) (success.wire.frontiers 0)
    (success.wire.frontiers 1) success.trace success.verified

theorem successful_record_is_body_record
    (view : RawHashInput → Digest208) (queries : Fin 22 → Position)
    (body : List Byte) (success : SuccessfulMerkleRun view queries body)
    (i : Fin 22) :
    success.wire.record i = PackedQueryRecord.bodyRecord body i :=
  SelectedWireBytes.record_eq_bodyRecord body success.wire success.parsed i

#print axioms successful_constructs_accepted
#print axioms successful_record_is_body_record
end AspisV8.SelectedWireMerkleRun
