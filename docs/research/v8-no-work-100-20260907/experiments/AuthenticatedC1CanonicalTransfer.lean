import AuthenticatedEarlyC1Prefix
import SelectedSemanticTransferV2

/-!
Construct canonical coefficients of the SAME member of the family attached
to the literal early-prefix extracted C1 word. V7 proves this totalized word
is base-valued even at unavailable/noncanonical raw entries. Own-support
descent then proves that re-embedding the constructed coefficients recovers
all26 member lanes, not merely its first16 projected coordinates.

The source decoder scans16 coefficient columns of length1024. Its exact
shape/canonical Boolean guard is discharged here; bit/pair/payment validation
are not identified with that preliminary guard. The existing selected
semantic and copy premises yield TransferFacts or one copy collision, not
an assumed successful Rust decoder or full checked payment witness.
-/
set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 200
set_option maxHeartbeats 250000

namespace AspisV8.AuthenticatedC1CanonicalTransfer
open AspisFormal.ArithmetizationCore AspisFormal.HashMerkleModel
open AspisV5ComponentCQM31TowerExact
open AspisPool.V7MerkleQueryGrammar AspisPool.V7FixedWidth29TupleList
open AspisPool.V7ExtractedLaneWords AspisPool.V7C1SubfieldRecovery
open AspisV8.AuthenticatedEarlyC1Prefix AspisV8.EarlyC1Family
open AspisV8.EarlyC1CopyCollision AspisV8.SelectedEarlyC1Amounts
open AspisV8.SelectedEarlyC1PaymentFacts AspisV8.SelectedSemanticRows
open AspisV8.SelectedSemanticTransfer
noncomputable section

/-- Derived from literal strict-decode-or-zero totalization, not from a
claim that all committed leaves were canonical or available early. -/
theorem prefix_word_base (records : AnswerPrefix) (root : Digest208)
    (column : Fin 26) (index : Fin 1048576) :
    projectBase (fixedC1 records root column index) =
      fixedC1 records root column index :=
  projectBase_c1Received (prefixWords records root) column index

def coefficient (candidate : C1InitialMessages) (column : Fin 26)
    (row : Fin 1024) : Nat := (candidate column row).re.re.val

theorem coefficient_canonical (candidate : C1InitialMessages)
    (column : Fin 26) (row : Fin 1024) :
    coefficient candidate column row < 2147483647 :=
  ZMod.val_lt _

/-- Subfield descent uses this member's OWN support; no dominant earlyC1
selection, decoder membership, or common support with another tuple is used. -/
theorem coefficient_reembeds (records : AnswerPrefix) (root : Digest208)
    (candidate : C1InitialMessages)
    (member : candidate ∈ family (fixedC1 records root))
    (column : Fin 26) (row : Fin 1024) :
    embedM31Exact (coefficient candidate column row : M31Exact) =
      candidate column row := by
  have fixed := congrFun (member_is_base (fixedC1 records root) candidate member
    (prefix_word_base records root) column) row
  change embedM31Exact (candidate column row).re.re = candidate column row at fixed
  simpa only [coefficient, ZMod.natCast_zmod_val] using fixed

/-- Canonical raw representatives are unique, rather than chosen modulo P.
This theorem does not assert uniqueness of the early family itself. -/
theorem canonical_coefficients_unique (candidate : C1InitialMessages)
    (raw : Fin 26 → Fin 1024 → Nat)
    (canonical : ∀ column row, raw column row < 2147483647)
    (represents : ∀ column row,
      embedM31Exact (raw column row : M31Exact) = candidate column row) :
    raw = coefficient candidate := by
  funext column row
  have base : (raw column row : M31Exact) = (candidate column row).re.re :=
    congrArg (fun value : QM31Exact => value.re.re) (represents column row)
  have representative := congrArg (fun value : M31Exact => value.val) base
  rw [ZMod.val_natCast_of_lt (canonical column row)] at representative
  exact representative

/-- StateOnlyTraceFoundation contains16 semantic columns, not all26
committed columns. The other ten recovered lanes are not zeroed or scanned. -/
def decoderColumn (candidate : C1InitialMessages) (column : Fin 16) : List Nat :=
  List.ofFn (fun row : Fin 1024 =>
    coefficient candidate ⟨column.val, by omega⟩ row)

theorem decoder_column_length (candidate : C1InitialMessages) (column : Fin 16) :
    (decoderColumn candidate column).length = 1024 := List.length_ofFn

/-- Literal Boolean shape/canonical guard at recovered_witness.rs:45,
modeled on the constructed coefficient vectors, not on authenticated bytes. -/
def decoderRejects (columns : Fin 16 → List Nat) : Bool :=
  (List.ofFn columns).any (fun column =>
    column.length != 1024 || column.any (fun raw => decide (2147483647 ≤ raw)))

theorem decoder_shape_canonical_passes (candidate : C1InitialMessages) :
    decoderRejects (decoderColumn candidate) = false := by
  apply List.any_eq_false.mpr
  intro column present
  obtain ⟨index, rfl⟩ := List.mem_ofFn.mp present
  have inner : (decoderColumn candidate index).any
      (fun raw => decide (2147483647 ≤ raw)) = false := by
    apply List.any_eq_false.mpr
    intro raw member
    obtain ⟨row, rfl⟩ := List.mem_ofFn.mp member
    simpa only [decide_eq_true_eq, not_le] using
      coefficient_canonical candidate ⟨index.val, by omega⟩ row
  simp only [decoder_column_length, bne_self_eq_false, Bool.false_or, inner,
    Bool.false_eq_true, not_false_eq_true]

theorem decoder_column_read (candidate : C1InitialMessages)
    (column : Fin 16) (row : Fin 1024) :
    (decoderColumn candidate column)[row.val]? =
      some (coefficient candidate ⟨column.val, by omega⟩ row) := by
  simp only [decoderColumn, List.getElem?_ofFn, dif_pos row.isLt]

/-- The source get(row,col) convention reads exactly the semanticTable
already used by all selected payment fragments, with no supplied trace map. -/
theorem decoder_read_is_semantic (candidate : C1InitialMessages)
    (column : Fin 16) (row : Fin 1024) :
    (coefficient candidate ⟨column.val, by omega⟩ row : F) =
      semanticTable candidate row.val column.val := by
  rw [semanticTable_read, memberTable_read]
  exact ZMod.natCast_zmod_val _

/-- Canonical construction plus the current maximal same-table payment
fragment. Source authentication-to-prefix agreement, sufficient own support,
full semantic/copy enforcement and external caller/settlement authority are
not inferred. In particular TransferFacts is not a checked witness. -/
theorem prefix_member_canonical_transfer
    (records : AnswerPrefix) (root : Digest208)
    (rc : RoundConstants) (pub : Public) (candidate : C1InitialMessages)
    (member : candidate ∈ family (fixedC1 records root))
    (lambdas chis : Finset QM31Exact) (lambda chi : QM31Exact)
    (lambdaMember : lambda ∈ lambdas) (chiMember : chi ∈ chis)
    (helper : Fin 1024 → QM31Exact)
    (copy : CopyConditions candidate .transfer pub.appendIndex lambda chi helper)
    (packedZero : ∀ row group, packedRows pub (semanticTable candidate) row group = 0)
    (poseidon : PoseidonChecks rc (semanticTable candidate)) :
    decoderRejects (decoderColumn candidate) = false ∧
    (∀ column row, embedM31Exact (coefficient candidate column row : M31Exact) =
      candidate column row) ∧
    (TransferFacts rc candidate pub.asset pub.nullifier pub.commitments ∨
      (lambda, chi) ∈ collisionPairs (fixedC1 records root) .transfer
        pub.appendIndex lambdas chis) := by
  refine ⟨decoder_shape_canonical_passes candidate,
    coefficient_reembeds records root candidate member, ?_⟩
  exact (member_transfer_or_copy_collision rc pub (fixedC1 records root) candidate
    member (prefix_word_base records root) lambdas chis lambda chi lambdaMember
    chiMember helper copy packedZero poseidon).2

#print axioms prefix_word_base
#print axioms coefficient_canonical
#print axioms coefficient_reembeds
#print axioms canonical_coefficients_unique
#print axioms decoder_column_length
#print axioms decoder_shape_canonical_passes
#print axioms decoder_column_read
#print axioms decoder_read_is_semantic
#print axioms prefix_member_canonical_transfer
end
end AspisV8.AuthenticatedC1CanonicalTransfer
