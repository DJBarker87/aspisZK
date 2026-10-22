import MultiproofConeP6Verify

set_option autoImplicit false
noncomputable section
namespace AspisR1.MultiproofConeP6Batch
open Aeneas Aeneas.Std Result MultiproofConeRef
open MultiproofConePhysicalProgram MultiproofConePhysicalTransport MultiproofConePhysicalViews
open MultiproofConeP6Composition MultiproofConeLeafFold MultiproofConeSlotTail
open OraclePortFrozenOrder OraclePortSelectedDraft OraclePortCompactDraft
open AspisV8R19.DuplexFrames AspisV8R19.SourceDuplexStep
open AspisV8R19.SqueezeOracleBridge
open AspisV8R19.MemoizedProgramLaw AspisV8R19.OracleProgramOps
attribute [local instance] Classical.propDecidable

abbrev Leaf := Parsed → (Fin 22 → Fin 262144) → Nat → Nat → reference.Scratch →
  Program Bytes State (Result (Option reference.Scratch))

def referenceLeaf (p : Parsed) (q : Fin 22 → Fin 262144) (kind pos : Nat)
    (s : reference.Scratch) : Program Bytes State (Result (Option reference.Scratch)) :=
  .ask (leaf p kind pos) fun d => .done (reference.leaf_step s (key q kind pos) (encodeState d))

/-- The verified leaf-hash and immediate dedup/write gates at their exact
local capacity domain. No duplicate-consistency premise is introduced. -/
def LeafGate (H : Bytes → State) (source : Leaf) : Prop :=
  ∀ p q kind pos s, s.n.val<16 →
    eval H (source p q kind pos s)=eval H (referenceLeaf p q kind pos s)

def leaves (source : Leaf) (p : Parsed) (q : Fin 22 → Fin 262144) (kind : Nat) :
    List Nat → reference.Scratch → Program Bytes State (Result (Option reference.Scratch))
  | [],s => .done (ok (some s))
  | pos::rest,s => bind (source p q kind pos s) fun result => match result with
    | .fail e => .done (.fail e)
    | .div => .done .div
    | .ok none => .done (ok none)
    | .ok (some t) => leaves source p q kind rest t

/-- Complete leaf fold from the local hash/dedup gate; keeps the full scratch
and the rejected suffix's absence, rather than only comparing Live roots. -/
theorem leaves_eq (H : Bytes → State) (source : Leaf) (gate : LeafGate H source)
    (p : Parsed) (q : Fin 22 → Fin 262144) (kind : Nat) (ps : List Nat)
    (s : reference.Scratch) (room : s.n.val+ps.length≤16) :
    eval H (leaves source p q kind ps s)=eval H (MultiproofConeLeafFold.leaves p q kind ps s) := by
  induction ps generalizing s with
  | nil => rfl
  | cons pos rest ih =>
    have bound : s.n.val<16 := by simp only [List.length_cons] at room;omega
    have step := MultiproofConeLeafContent.step_exact s (key q kind pos)
      (encodeState (H (leaf p kind pos))) bound
    simp only [leaves,eval_bind,gate p q kind pos s bound,referenceLeaf,
      MultiproofConeLeafFold.leaves,eval,step]
    cases result : MultiproofConeLeafContent.next s (key q kind pos)
        (encodeState (H (leaf p kind pos))) bound with
    | none => simp only [result,eval,List.append_nil]
    | some t =>
      have tb := next_bound s (key q kind pos) (encodeState (H (leaf p kind pos))) bound t result
      simp only [result,List.singleton_append]
      rw [ih t (by simp only [List.length_cons] at room;omega)]

def tailState (nodeSource : Node) (p : Parsed) (batch kind : Nat)
    (nodes : Slice U8) (s : reference.Scratch) : Program Bytes State (Bool × reference.Scratch) :=
  let is := (live s 0 s.n.val).map Prod.fst
  if wellFormed is then
    let count := slotCount s
    let cap := capacity (3*batch+kind)
    let bs := MultiproofConeCanonical.bytesOf nodes.val
    if count≤cap ∧ bs.length=32*cap ∧
        MultiproofConePadding.scan (4*(cap-count)) (bs.drop (32*count))=true then
      MultiproofConeP6Verify.verifyState nodeSource
        (encodeState (OraclePortBatchDraft.committedRoot p kind))
        (prefixNodes nodes count) {s with «at»:=0#usize}
    else .done (false,s)
  else .done (false,s)

theorem tailState_eq {X : Type} (D : aspis_core.digest.Digest32 X) (hash : X)
    (H : Bytes → State) (law : ∀ input, D.digest hash input=ok (rawOracle H input))
    (source : Node) (gate : NodeGate (rawOracle H) source)
    (p : Parsed) (batch kind : Nat) (nodes : Slice U8) (size : nodes.val.length≤5504)
    (s : reference.Scratch) :
    eval H (tailState source p batch kind nodes s)=
      eval H (MultiproofConeVerifyState.tailState p batch kind nodes s) := by
  unfold tailState MultiproofConeVerifyState.tailState
  dsimp only
  split
  · split
    · exact MultiproofConeP6Verify.verifyState_eq D hash H law source gate _ _
        (by simp only [prefixNodes,List.length_take];omega) _ rfl
    · rfl
  · rfl

/-- batch_tree denotation at P6's packed-key/opening/control/library cut.
The leaf gate is called once per sorted opening, before its duplicate check.
Count, padding and root remain in their actual chronological positions. -/
def batch_tree (nodeSource : Node) (leafSource : Leaf)
    (p : Parsed) (q : Fin 22 → Fin 262144) (batch kind : Nat)
    (nodes : Slice U8) (s : reference.Scratch) : Program Bytes State (Bool × reference.Scratch) :=
  bind (leaves leafSource p q kind (sortedPositions q batch kind) (MultiproofConeSlotState.reset s)) fun out =>
    match out with
    | .ok (some after) => tailState nodeSource p batch kind nodes after
    | _ => .done (false,s)

/-- Whole batch equality to the owned instrumented reference on every input
in the admitted fixed-slot domain. Only LOCAL P6 contracts are retained;
no per-batch equality, acceptance, leaf success or node success is assumed. -/
theorem batch_tree_owned {X : Type} (D : aspis_core.digest.Digest32 X) (hash : X)
    (H : Bytes → State) (law : ∀ input, D.digest hash input=ok (rawOracle H input))
    (nodeSource : Node) (nodeGate : NodeGate (rawOracle H) nodeSource)
    (leafSource : Leaf) (leafGate : LeafGate H leafSource)
    (p : Parsed) (q : Fin 22 → Fin 262144) (batch kind : Nat)
    (nodes : Slice U8) (size : nodes.val.length≤5504) (s : reference.Scratch) :
    eval H (batch_tree nodeSource leafSource p q batch kind nodes s)=
      eval H (MultiproofConeSlotState.slotState p q batch kind nodes s) := by
  have room : (MultiproofConeSlotState.reset s).n.val+(sortedPositions q batch kind).length≤16 := by
    have bound := MultiproofConeLeafFrozen.sorted_length q batch kind
    change 0+_≤16;omega
  simp only [batch_tree,MultiproofConeSlotState.slotState,eval_bind,
    leaves_eq H leafSource leafGate p q kind _ _ room]
  cases (eval H (MultiproofConeLeafFold.leaves p q kind (sortedPositions q batch kind)
      (MultiproofConeSlotState.reset s))).2 with
  | fail e => rfl
  | div => rfl
  | ok out =>
    cases out with
    | none => rfl
    | some after => rw [tailState_eq D hash H law nodeSource nodeGate p batch kind nodes size after]

#print axioms leaves_eq
#print axioms tailState_eq
#print axioms batch_tree_owned
end AspisR1.MultiproofConeP6Batch
end
