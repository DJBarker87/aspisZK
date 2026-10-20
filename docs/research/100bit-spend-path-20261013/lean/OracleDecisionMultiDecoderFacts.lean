import OracleDecisionMultiTree
import BinHonestStartFrames

/-! A concrete decoder counterexample: a literal binary-node preimage can be
an ordinary row-one absorb address. The table is finite (three earlier
transcript cells, plus one leaf cell). No huge address universe is evaluated.
This refutes first-byte separation as a zero-start argument. -/
set_option autoImplicit false
noncomputable section
namespace AspisR1.OracleDecisionMultiDecoder
open FS FS2 FS2.Duplex R0C.V3 AspisV8PairedCommitment
open AspisV8R19.DuplexFrames AspisV8R19.SourceDuplexStep
open AspisV8R19.MemoizedProgramLaw AspisV8R19.OracleProgramOps
open AspisV8R19.AdaptiveFirstReadLaw
open CanonicalAddressEmbedding
open OracleDecisionMultiTree
abbrev p := SelectedTranscriptParams.params
abbrev L := SelectedTranscriptParams.L

def pub : LiteralTranscript.Public := ⟨[], by decide, 2⟩
def s0 : State := fun _ => 3
def absorbed : State := fun _ => 4
def endpoint : State := fun i => if i = 0 then 18 else 0
def zero : State := fun _ => 0
def right : State := fun i => if i = 0 then 161 else 0

def initial : Addr L := PublicInitFrame.addr [] (by decide) zero
def row0 : Addr L := PublicInitFrame.row0 p (by norm_num [p, SelectedTranscriptParams.params,
  SelectedTranscriptParams.D]) s0
def advanced : Addr L := advanceA p absorbed
def leaf : Bytes := BinMerkle32Leaf.leafInput 0xf1 (List.replicate 128 1) (List.replicate 32 1)
def node : Bytes := BinMerkle32Path.nodeInput (children zero right)
def nodeAddr : Addr L := absorbA p endpoint (p.lbl 1) (List.replicate 31 0) (by decide)

def table : Table Bytes State := fun b =>
  if b = initial.toBytes then some s0 else
  if b = row0.toBytes then some absorbed else
  if b = advanced.toBytes then some endpoint else
  if b = leaf then some zero else none

/-- Equality of two 65-byte literal grammars. No recurrence or large set. -/
theorem node_absorb : node = bytes endpoint ++ [0, p.lbl 1] ++ List.replicate 31 0 := by
  decide

theorem byte_lengths : initial.toBytes.length = 75 ∧ row0.toBytes.length = 39 ∧
    advanced.toBytes.length = 33 ∧ leaf.length = 162 ∧ node.length = 65 := by
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · simp only [initial, PublicInitFrame.addr_bytes]
    decide
  · simp [row0, PublicInitFrame.row0, absorbA, Addr.toBytes_ofBytes, absorb,
      bytes_length, PublicInitFrame.emptyRecord]
  · simp [advanced, advanceA, Addr.toBytes_ofBytes, advance, bytes_length]
  · change (BinMerkle32Leaf.leafInput 0xf1 (List.replicate 128 1) (List.replicate 32 1)).length = 162
    rw [BinMerkle32Leaf.leaf_input_length 0xf1 _ _ (by simp)]
    simp only [List.length_replicate]
  · exact BinMerkle32Path.nodeInput_length _

theorem state_distinct : s0 ≠ absorbed ∧ s0 ≠ endpoint ∧ s0 ≠ zero ∧
    absorbed ≠ endpoint ∧ absorbed ≠ zero ∧ endpoint ≠ zero := by
  decide

theorem table_fibers :
    (∀ b, table b = some s0 ↔ b = initial.toBytes) ∧
    (∀ b, table b = some absorbed ↔ b = row0.toBytes) ∧
    (∀ b, table b = some endpoint ↔ b = advanced.toBytes) := by
  have hl := byte_lengths
  have h01 : initial.toBytes ≠ row0.toBytes := by intro h; have := congrArg List.length h; omega
  have h02 : initial.toBytes ≠ advanced.toBytes := by intro h; have := congrArg List.length h; omega
  have h12 : row0.toBytes ≠ advanced.toBytes := by intro h; have := congrArg List.length h; omega
  rcases state_distinct with ⟨hsa,hse,hsz,hae,haz,hez⟩
  refine ⟨?_, ?_, ?_⟩ <;> intro b <;> unfold table <;>
    split_ifs <;> simp_all only [Option.some.injEq, reduceCtorEq,
      Ne.symm hsa, Ne.symm hse, Ne.symm hsz, Ne.symm hae, Ne.symm haz, Ne.symm hez]

/-- Transport a singleton raw-output fiber, without enumerating Addr L. -/
theorem bounded_fiber (T : Table Bytes State) (a0 : Addr L)
    (hc : CanonicalByteAddress.Canonical a0) (v : State)
    (hf : ∀ b, T b = some v ↔ b = a0.toBytes) (a : Addr L) :
    RawBoundedTrace.table L T a = some v ↔ a = a0 := by
  by_cases ha : CanonicalByteAddress.Canonical a
  · rw [RawBoundedTrace.table_canonical L T a ha, hf]
    constructor
    · intro he
      exact congrArg Subtype.val (CanonicalAddressEmbedding.toBytes_injective
        (a₁ := ⟨a,ha⟩) (a₂ := ⟨a0,hc⟩) he)
    · rintro rfl; rfl
  · rw [RawBoundedTrace.table_noncanonical L T a ha]
    simp only [reduceCtorEq, false_iff]
    intro he; subst a; exact ha hc

theorem bounded_fibers :
    (∀ a, RawBoundedTrace.table L table a = some s0 ↔ a = initial) ∧
    (∀ a, RawBoundedTrace.table L table a = some absorbed ↔ a = row0) ∧
    (∀ a, RawBoundedTrace.table L table a = some endpoint ↔ a = advanced) := by
  refine ⟨bounded_fiber table initial ?_ s0 table_fibers.1,
    bounded_fiber table row0 ?_ absorbed table_fibers.2.1,
    bounded_fiber table advanced ?_ endpoint table_fibers.2.2⟩
  · unfold initial PublicInitFrame.addr; apply CanonicalByteAddress.canonical_ofBytes
  · unfold row0 PublicInitFrame.row0 absorbA; apply CanonicalByteAddress.canonical_ofBytes
  · unfold advanced advanceA; apply CanonicalByteAddress.canonical_ofBytes

theorem lookups :
    ReseedBoundary.findCell (RawBoundedTrace.table L table) s0 = some initial ∧
    ReseedBoundary.findCell (RawBoundedTrace.table L table) absorbed = some row0 ∧
    theUnique (advPre p (RawBoundedTrace.table L table) endpoint) = some absorbed := by
  classical
  refine ⟨?_, ?_, ?_⟩
  · unfold ReseedBoundary.findCell
    rw [theUnique_eq_some]
    ext a
    simpa only [cellsWith, Finset.mem_filter, Finset.mem_univ, true_and,
      and_true, Finset.mem_singleton] using bounded_fibers.1 a
  · unfold ReseedBoundary.findCell
    rw [theUnique_eq_some]
    ext a
    simpa only [cellsWith, Finset.mem_filter, Finset.mem_univ, true_and,
      and_true, Finset.mem_singleton] using bounded_fibers.2.1 a
  · rw [theUnique_eq_some]
    ext s
    simp only [advPre, preimages, Finset.mem_filter, Finset.mem_univ, true_and,
      Finset.mem_singleton, bounded_fibers.2.2]
    exact ⟨fun h => advanceA_injective p h, fun h => congrArg (advanceA p) h⟩


#print axioms node_absorb
#print axioms byte_lengths
#print axioms state_distinct
#print axioms table_fibers
#print axioms bounded_fiber
#print axioms bounded_fibers
#print axioms lookups
end AspisR1.OracleDecisionMultiDecoder
end
