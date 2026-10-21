import OraclePortBatchDraft

/-!
Source-shaped binary slot, additive draft only. Source citations (frozen base):
* candidate.rs:99-113, 173-195: keys (index << 8 | relative position), sorted
  ascending; hash EVERY leaf, reject unequal duplicate digests immediately.
* candidate.rs:196-202: node_count, capacity/whole-word zero padding, verify.
* multiproof.rs:58-62, 96-122: index validation and supplied-node counting.
* multiproof.rs:151-213: initial checks, levels in ascending order, parents in
  ascending index order, consecutive sibling consumption, final root/length.

Lists represent only the live prefixes of the caller-owned arrays. A level
reads a group before appending its parent to the next live prefix: this is
exactly the non-overwriting read/write schedule (w <= i) of the in-place loop.
The arithmetic uses Nat at the fixed bounded source indices, not machine wrap.
This definition is not a proved Rust extraction/caller join.
-/
set_option autoImplicit false
noncomputable section
namespace AspisR1.OraclePortInnerOrderFrozen
open FS FS2
open AspisV8R19.DuplexFrames AspisV8R19.SourceDuplexStep
open AspisV8R19.MemoizedProgramLaw AspisV8R19.OracleProgramOps
open OraclePortCompactDraft OraclePortSelectedDraft OracleDecisionMultiTree
attribute [local instance] Classical.propDecidable

abbrev Live := List (Nat × State)

/-- Absolute positions have the same ascending tie order as source lo+position. -/
def sortedPositions (q : Fin 22 → Fin 262144) (batch kind : Nat) : List Nat :=
  (batchPositions batch).mergeSort (fun a b => decide
    (index q kind a < index q kind b ∨ index q kind a = index q kind b ∧ a ≤ b))

/-- Reversed live scratch prefix; the last unique digest is checked immediately. -/
def hashLeaves (p : Parsed) (q : Fin 22 → Fin 262144) (kind : Nat) :
    List Nat → Live → Program Bytes State (Option Live)
  | [], rev => .done (some rev.reverse)
  | pos::rest, rev => .ask (leaf p kind pos) fun d =>
      let i := index q kind pos
      match rev with
      | (j,v)::tail => if i = j then
          if d = v then hashLeaves p q kind rest rev else .done none
        else hashLeaves p q kind rest ((i,d)::(j,v)::tail)
      | [] => hashLeaves p q kind rest [(i,d)]

/-- The consecutive occupied sibling condition, on a validated sorted prefix. -/
def paired (i j : Nat) : Prop := i % 2 = 0 ∧ j = i+1

/-- Pure index-only node_count step. Lists shrink structurally via fuel. -/
def countLevel : Nat → List Nat → List Nat × Nat
  | 0, _ => ([],0)
  | _+1, [] => ([],0)
  | fuel+1, i::rest =>
      let both := match rest with | j::_ => decide (paired i j) | [] => false
      let out := countLevel fuel (if both then rest.drop 1 else rest)
      (i/2 :: out.1, out.2 + if both then 0 else 1)

def nodeCount : Nat → List Nat → Nat
  | 0, _ => 0
  | h+1, is => let out := countLevel is.length is
              out.2 + nodeCount h out.1

def wellFormed (is : List Nat) : Prop :=
  is ≠ [] ∧ is.length ≤ 16 ∧ is.Pairwise (· < ·) ∧ ∀ i ∈ is, i < 262144

/-- One source level. A short sibling slice exits before issuing its hash. -/
def runLevel : Nat → Live → Bytes → Program Bytes State (Option (Live × Bytes))
  | 0, _, nodes => .done (some ([],nodes))
  | _+1, [], nodes => .done (some ([],nodes))
  | fuel+1, (i,v)::rest, nodes =>
      let both := match rest with | (j,_)::_ => decide (paired i j) | [] => false
      if both then
        let right := (rest.head!).2
        .ask (BinMerkle32Path.nodeInput (children v right)) fun d =>
          bind (runLevel fuel (rest.drop 1) nodes) fun out =>
            .done (out.map fun x => ((i/2,d)::x.1,x.2))
      else match SemanticRecordCodec.decodeState (nodes.take 32) with
        | none => .done none
        | some sibling =>
          let pair := if i % 2 = 0 then children v sibling else children sibling v
          .ask (BinMerkle32Path.nodeInput pair) fun d =>
            bind (runLevel fuel rest (nodes.drop 32)) fun out =>
              .done (out.map fun x => ((i/2,d)::x.1,x.2))

/-- Eighteen levels are instantiated only at the slot boundary. -/
def runLevels : Nat → Live → Bytes → Program Bytes State (Option (Live × Bytes))
  | 0, live, nodes => .done (some (live,nodes))
  | h+1, live, nodes => bind (runLevel live.length live nodes) fun out =>
      match out with
      | none => .done none
      | some (next,remaining) => runLevels h next remaining

def verifyInPlace (root : State) (live : Live) (nodes : Bytes) : Program Bytes State Bool :=
  if wellFormed (live.map Prod.fst) ∧ nodes.length % 32 = 0 then
    bind (runLevels 18 live nodes) fun out => .done (match out with
      | some ([(i,d)],remaining) => decide (i = 0 ∧ d = root ∧ remaining = [])
      | _ => false)
  else .done false

/-- The per-slot guard is deliberately inside the leaf continuation. The source
slot is a fixed-width slice under its upstream proof-size check. The explicit
width test makes this helper total on arbitrary Parsed values, rejecting short
slices instead of Rust's unreachable indexing panic. -/
def slotTail (p : Parsed) (batch kind : Nat) (live : Live) : Program Bytes State Bool :=
  let is := live.map Prod.fst
  if wellFormed is then
    let count := nodeCount 18 is
    let cap := capacity (3*batch+kind)
    let nodes := slice p.wire (slotStart (3*batch+kind)) (32*cap)
    if count ≤ cap ∧ nodes.length = 32*cap ∧
        nodes.drop (32*count) = List.replicate (32*(cap-count)) 0 then
      verifyInPlace (OraclePortBatchDraft.committedRoot p kind) live (nodes.take (32*count))
    else .done false
  else .done false

def verifySlot_frozen (p : Parsed) (q : Fin 22 → Fin 262144) (batch kind : Nat) :
    Program Bytes State Bool :=
  bind (hashLeaves p q kind (sortedPositions q batch kind) []) fun out =>
    match out with
    | none => .done false
    | some live => slotTail p batch kind live

/-- Generic height step, without normalizing any height-18 tree. -/
theorem levels_step (H : Bytes → State) (h : Nat) (live : Live) (nodes : Bytes) :
    eval H (runLevels (h+1) live nodes) =
      ((eval H (runLevel live.length live nodes)).1 ++
        (eval H (match (eval H (runLevel live.length live nodes)).2 with
          | none => .done none
          | some (next,remaining) => runLevels h next remaining)).1,
       (eval H (match (eval H (runLevel live.length live nodes)).2 with
          | none => .done none
          | some (next,remaining) => runLevels h next remaining)).2) := by
  simp only [runLevels,eval_bind]

#print axioms levels_step
end AspisR1.OraclePortInnerOrderFrozen
end
