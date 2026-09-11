import PackedQueryRecord
import NearGammaSelectedC1

/-!
Paired prefix projections of ONE successfully parsed packed record imply
the literal gamma-batched received word at its four child slots. The C1
and C2 words are separate inputs: they may come from different causal
prefix cutoffs. No root-alone extraction, authentication, global canonical
decoding, or received-word polynomiality is assumed or proved here.

Reuses V7ExtractedLaneWords' successful-projection decoder lemmas and its
literal fibre/slot indexing, plus PackedQueryRecord's exact parser theorem.
-/
set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 200
set_option maxHeartbeats 200000

namespace AspisV8.PrefixPackedQueryBatch
noncomputable section
open AspisV5ComponentCQM31TowerExact
open AspisV5ComponentCConcreteFoldLinearity
open AspisPool.V7MerkleQueryGrammar AspisPool.V7MerkleQueryExtractor
open AspisPool.V7ExtractedLaneWords AspisPool.V7C1ConcreteProjectionBinding
open AspisV8.PackedQueryRecord AspisV8.EarlyC1LateProjection
open scoped BigOperators

abbrev K := QM31Exact

/-- Each authenticated phase projects the SAME raw record, including the
source's common salt. These are projection premises, not consequences of
canonical parsing or an arbitrarily selected post-query total word. -/
def PairedProjection (first second : ExtractedWords) (fibre : Fin 262144)
    (record : List Byte) : Prop :=
  first.c1[fibre.val]? = some ⟨c1Bytes record, saltBytes record⟩ ∧
    second.c2[fibre.val]? = some ⟨c2Bytes record, saltBytes record⟩

theorem c1_slot_of_projection
    (first : ExtractedWords) (fibre : Fin 262144)
    (record : List Byte) (decoded : Decoded)
    (parsed : parse record = some decoded)
    (projection : first.c1[fibre.val]? =
      some ⟨c1Bytes record, saltBytes record⟩)
    (slot : Fin 4) (column : Fin 26) :
    c1Received first column (initialIndex fibre slot) =
      algebraMap M31Exact K (baseValue decoded slot column) := by
  have projected : first.c1[(fibreIndex (initialIndex fibre slot)).val]? =
      some ⟨c1Bytes record, saltBytes record⟩ := by
    simpa only [fibreIndex_initialIndex] using projection
  have entry : AspisPool.V7PackedFibreTowerBridge.decodeC1EntryExact
      (c1Bytes record) (fibreSlot (initialIndex fibre slot)) column =
        some (baseValue decoded slot column) := by
    simpa only [fibreSlot_initialIndex] using
      c1_entry record decoded parsed slot column
  exact (c1_received_of_exact_projection first (initialIndex fibre slot) column
    ⟨c1Bytes record, saltBytes record⟩ (baseValue decoded slot column)
    projected entry).trans (embedM31Exact_eq_algebraMap _)

theorem c2_slot_of_projection
    (second : ExtractedWords) (fibre : Fin 262144)
    (record : List Byte) (decoded : Decoded)
    (parsed : parse record = some decoded)
    (projection : second.c2[fibre.val]? =
      some ⟨c2Bytes record, saltBytes record⟩)
    (slot : Fin 4) (helper : Fin 3) :
    c2Received second helper (initialIndex fibre slot) =
      helperValue decoded helper slot := by
  have projected : second.c2[(fibreIndex (initialIndex fibre slot)).val]? =
      some ⟨c2Bytes record, saltBytes record⟩ := by
    simpa only [fibreIndex_initialIndex] using projection
  have entry : AspisPool.V7PackedFibreTowerBridge.decodeC2EntryExact
      (c2Bytes record) helper (fibreSlot (initialIndex fibre slot)) =
        some (helperValue decoded helper slot) := by
    simpa only [fibreSlot_initialIndex] using
      c2_entry record decoded parsed helper slot
  exact c2_received_of_exact_projection second (initialIndex fibre slot) helper
    ⟨c2Bytes record, saltBytes record⟩ (helperValue decoded helper slot)
    projected entry

/-- Literal 26 base lanes followed by H/G/D, at an arbitrary one of the
four source-ordered slots. No challenge has yet been used. -/
theorem lanes_of_paired_projection
    (first second : ExtractedWords) (fibre : Fin 262144)
    (record : List Byte) (decoded : Decoded)
    (parsed : parse record = some decoded)
    (projection : PairedProjection first second fibre record)
    (slot : Fin 4) (lane : Fin 29) :
    received29 (c1Received first) (c2Received second) lane
      (initialIndex fibre slot) = laneValue decoded slot lane := by
  unfold received29 laneValue
  split
  · exact c1_slot_of_projection first fibre record decoded parsed projection.1 slot _
  · exact c2_slot_of_projection second fibre record decoded parsed projection.2 slot _

/-- The exact selected raw-word / parsed-value equality, uniformly for ALL
gamma (including zero) and ALL four child slots. Child address is 4*fibre+slot.
This is the pointwise equality required by FixedWordQueryTerminal.OpeningEquality.
-/
theorem batch_slots_of_paired_projection
    (first second : ExtractedWords) (fibre : Fin 262144)
    (record : List Byte) (decoded : Decoded)
    (parsed : parse record = some decoded)
    (projection : PairedProjection first second fibre record)
    (gamma : K) (slot : Fin 4) :
    NearGammaSelectedC1.rawBatch (c1Received first) (c2Received second) gamma
      (childIndex fibre slot) = combined gamma decoded slot := by
  change (∑ lane : Fin 29, gamma ^ lane.val *
      received29 (c1Received first) (c2Received second) lane
        (initialIndex fibre slot)) = combined gamma decoded slot
  rw [combined_eq_scalar_power]
  apply Finset.sum_congr rfl
  intro lane _
  rw [lanes_of_paired_projection first second fibre record decoded parsed
    projection slot lane]

/-- Raw-record endpoint. Successful canonical parsing is retained, so the
totalized raw decoder cannot turn an invalid queried limb into acceptance. -/
theorem raw_slots_of_paired_projection
    (first second : ExtractedWords) (fibre : Fin 262144)
    (record : List Byte) (decoded : Decoded)
    (parsed : parse record = some decoded)
    (projection : PairedProjection first second fibre record)
    (gamma : K) (slot : Fin 4) :
    NearGammaSelectedC1.rawBatch (c1Received first) (c2Received second) gamma
      (childIndex fibre slot) = rawCombined gamma record slot :=
  (batch_slots_of_paired_projection first second fibre record decoded parsed
    projection gamma slot).trans (combined_eq_raw record decoded parsed gamma slot)

#print axioms c1_slot_of_projection
#print axioms c2_slot_of_projection
#print axioms lanes_of_paired_projection
#print axioms batch_slots_of_paired_projection
#print axioms raw_slots_of_paired_projection
end
end AspisV8.PrefixPackedQueryBatch
