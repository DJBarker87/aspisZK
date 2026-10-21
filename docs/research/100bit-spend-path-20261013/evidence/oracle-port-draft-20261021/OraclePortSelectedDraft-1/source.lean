import OraclePortCompactDraft
import OracleDecisionMultiRecovery

/-! Query-selected, occupied, depth-18 authentication trees. All indices and
leaf preimages are derived from the same reached transcript and stored bytes.
The sibling order is the frozen level order, not the execution's postorder. -/
set_option autoImplicit false
noncomputable section
namespace AspisR1.OraclePortSelectedDraft
open FS FS2
open AspisV8R19.DuplexFrames AspisV8R19.SourceDuplexStep
open OraclePortCompactDraft
open OracleDecisionMultiTree
open OracleDecisionMultiBuild
open OracleDecisionMultiRecovery (OpenedAt)
open RawCutTranscriptRun (ErasedPrefix)
attribute [local instance] Classical.propDecidable

/-- Public selected sampler result; it is not supplied as a forest parameter. -/
def queries (tr : ErasedPrefix) : Option (Fin 22 → Fin 262144) := do
  let (_, c) ← tr.rounds[31]?
  match c.1 with
  | .queries (.ok bs) => LiteralQueryRead.decode bs
  | _ => none

def batchPositions (batch : Nat) : List Nat :=
  if batch = 0 then List.range 10 else (List.range 12).map (·+10)

def index (q : Fin 22 → Fin 262144) (tree pos : Nat) : Nat :=
  let u := (q ⟨pos % 22, Nat.mod_lt _ (by decide)⟩).val
  if tree = 2 then u/4 else u

def selected (q : Fin 22 → Fin 262144) (batch tree : Nat) : List Nat :=
  (batchPositions batch).map (index q tree)

def opening (p : Parsed) (pos : Nat) : Bytes := slice p.wire (10055+pos*832) 832

def leaf (p : Parsed) (tree pos : Nat) : Bytes :=
  let b := opening p pos
  if tree = 0 then BinMerkle32Leaf.leafInput 0x71 (b.take 480) (slice b 608 32)
  else if tree = 1 then BinMerkle32Leaf.leafInput 0xf1 (slice b 480 128) (slice b 640 32)
  else BinMerkle32Leaf.leafInput 0x72 (slice b 672 128) (slice b 800 32)

/-- Pick the earliest source position, exactly the stable key tie breaker. -/
def position (q : Fin 22 → Fin 262144) (batch tree i : Nat) : Nat :=
  ((batchPositions batch).find? (fun pos => decide (index q tree pos = i))).getD 0

def input (p : Parsed) (q : Fin 22 → Fin 262144) (batch tree i : Nat) : Bytes :=
  leaf p tree (position q batch tree i)

/-- Sparse frontier: wholly unoccupied children consume one stored digest.
Only occupied branches are traversed. No 262144-cell enumeration occurs. -/
def frontier (is : List Nat) : Nat → Nat → List (Nat × Nat)
  | 0, base => if Occupied is 0 base then [] else [(0,base)]
  | h+1, base => if Occupied is (h+1) base then
      frontier is h base ++ frontier is h (base+2^h) else [(h+1,base)]

def orderedFrontier (is : List Nat) : List (Nat × Nat) :=
  (frontier is 18 0).mergeSort (fun a b => decide (a.1 < b.1 ∨ a.1 = b.1 ∧ a.2 ≤ b.2))

def capacity (s : Nat) : Nat := [146,146,128,172,172,150][s]?.getD 0

def slotStart (s : Nat) : Nat := 28359 + 32 * ((List.range s).map capacity).sum

def siblingBytes (p : Parsed) (q : Fin 22 → Fin 262144)
    (batch tree h base : Nat) : Bytes :=
  let order := orderedFrontier (selected q batch tree)
  let pos := order.idxOf (h,base)
  slice p.wire (slotStart (3*batch+tree)+32*pos) 32

/-- decodeState rejects wrong widths rather than accepting arbitrary state values. -/
def sibling (p : Parsed) (q : Fin 22 → Fin 262144)
    (batch tree h base : Nat) : State :=
  (SemanticRecordCodec.decodeState (siblingBytes p q batch tree h base)).getD (fun _ => 0)

def tree (p : Parsed) (q : Fin 22 → Fin 262144) (batch kind : Nat) : Tree :=
  build (selected q batch kind) (input p q batch kind) (sibling p q batch kind) 18 0

def Padding (p : Parsed) (q : Fin 22 → Fin 262144) : Prop :=
  ∀ batch ∈ List.range 2, ∀ kind ∈ List.range 3,
    let s := 3*batch+kind
    let count := (orderedFrontier (selected q batch kind)).length
    count ≤ capacity s ∧
    slice p.wire (slotStart s + 32*count) (32*(capacity s-count)) =
      List.replicate (32*(capacity s-count)) 0

theorem selected_occupied (q : Fin 22 → Fin 262144) (batch kind : Nat) :
    Occupied (selected q batch kind) 18 0 := by
  have hm (pos : Nat) : index q kind pos < 2^18 := by
    unfold index
    split
    · have ht := (q ⟨pos % 22, Nat.mod_lt _ (by decide)⟩).isLt
      omega
    · exact (q _).isLt
  refine ⟨index q kind (if batch = 0 then 0 else 10), ?_, Nat.zero_le _, hm _⟩
  apply List.mem_map.mpr
  refine ⟨if batch = 0 then 0 else 10, ?_, rfl⟩
  by_cases hb : batch = 0
  · simp [batchPositions,hb]
  · simp [batchPositions,hb]

theorem occupied_tree (p : Parsed) (q : Fin 22 → Fin 262144) (batch kind : Nat) :
    0 < leaves (tree p q batch kind) :=
  (leaves_positive_iff _ _ _ _ _).mpr (selected_occupied q batch kind)

/-- Generic routing lemma before any concrete 18-level instantiation. -/
theorem build_opened (is : List Nat) (f : Nat → Bytes) (s : Nat → Nat → State)
    (h base i : Nat) (hi : i ∈ is) (lo : base ≤ i) (upper : i < base+2^h) :
    ∃ slots, slots.length = h ∧ OpenedAt (build is f s h base) slots (f i) := by
  induction h generalizing base with
  | zero =>
    have eq : i = base := by omega
    subst i
    refine ⟨[],rfl,?_⟩
    rw [build, if_pos ((occupied_zero is base).mpr hi)]
    exact .leaf _
  | succ h ih =>
    have ho : Occupied is (h+1) base := ⟨i,hi,lo,upper⟩
    rw [build, if_pos ho]
    by_cases half : i < base+2^h
    · obtain ⟨slots,hlen,hopen⟩ := ih base lo half
      exact ⟨0::slots,by simp [hlen],.left hopen⟩
    · have low : base+2^h ≤ i := by omega
      have high : i < base+2^h+2^h := by
        rw [Nat.pow_succ] at upper
        omega
      obtain ⟨slots,hlen,hopen⟩ := ih (base+2^h) low high
      exact ⟨1::slots,by simp [hlen],.right hopen⟩

#print axioms selected_occupied
#print axioms occupied_tree
#print axioms build_opened
end AspisR1.OraclePortSelectedDraft
end
