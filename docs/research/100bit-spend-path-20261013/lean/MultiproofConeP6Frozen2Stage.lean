import MultiproofConeP6Callbacks
import MultiproofConeSlotAdapters

set_option autoImplicit false
noncomputable section
namespace AspisR1.MultiproofConeP6Frozen2Stage
open Aeneas Aeneas.Std Result MultiproofConeRef
open MultiproofConePhysicalProgram MultiproofConePhysicalTransport MultiproofConePhysicalDigest
open MultiproofConeP6Composition MultiproofConeP6Callbacks MultiproofConeP6Batch
open OraclePortFrozenOrder OraclePortSelectedDraft OraclePortCompactDraft
open AspisV8R19.DuplexFrames AspisV8R19.SourceDuplexStep
open AspisV8R19.MemoizedProgramLaw AspisV8R19.OracleProgramOps

-- Symbolic composition never needs to normalize a concrete height-18 run.
attribute [local irreducible] MultiproofConeP6Composition.levels
  MultiproofConeP6Composition.rows MultiproofConeP6Callbacks.nodeWith

/-- Named local P6 obligations only: oracle interpretation, the three
callback contracts and the single-leaf hash/dedup contract. No whole
verifier, batch, level, invariant or successful-output equality is a field.
The frozen-control/library interpretation of nodeWith/batch_tree is the
external P6 lowering boundary documented in P6-CERTIFICATES.md. -/
structure P6Boundary {X : Type} (D : aspis_core.digest.Digest32 X) (hash : X)
    (H : Bytes → State) (binary occupied sibling : Parent) (leafSource : Leaf) : Prop where
  oracle : ∀ input, D.digest hash input=ok (rawOracle H input)
  binary_parent : ParentGate (rawOracle H) binary
  occupied_parent : ParentGate (rawOracle H) occupied
  sibling_parent : ParentGate (rawOracle H) sibling
  leaf : LeafGate H leafSource

/-- Two whole-function certificates composed from the local P6 boundary.
The verifier compares the full generated owned Result. The batch compares
the full owned instrumented observation and scratch on all admitted inputs.
Neither conclusion is an assumed field of P6Boundary. -/
theorem function_certificates {X : Type} (D : aspis_core.digest.Digest32 X) (hash : X)
    (H : Bytes → State) (binary occupied sibling : Parent) (leafSource : Leaf)
    (p6 : P6Boundary D hash H binary occupied sibling leafSource) :
    (∀ (root : Digest) (s : reference.Scratch) (physical : Slice U8), physical.val.length≤5504 →
      MultiproofConeP6Verify.wrapper
        (fun state => (eval (rawOracle H) (levels (nodeWith occupied sibling) 18 state physical)).2)
        root s physical=reference.verify_owned D hash root s physical) ∧
    (∀ (p : Parsed) (q : Fin 22 → Fin 262144) (batch kind : Nat) (nodes : Slice U8),
      nodes.val.length≤5504 → ∀ s,
      eval H (batch_tree (nodeWith occupied sibling) leafSource p q batch kind nodes s)=
        eval H (MultiproofConeSlotState.slotState p q batch kind nodes s)) := by
  have nodes := node_gate (rawOracle H) occupied sibling p6.occupied_parent p6.sibling_parent
  constructor
  · intro root s physical size
    exact MultiproofConeP6Verify.verify_in_place_owned D hash (rawOracle H) p6.oracle
      (nodeWith occupied sibling) nodes root s physical size
  · intro p q batch kind physical size s
    exact batch_tree_owned D hash H p6.oracle _ nodes leafSource p6.leaf p q batch kind physical size s

#print axioms function_certificates

/-- Generic short-circuit composition keeps large callback terms out of
the induction motive and kernel definitional comparison. -/
def sequence (slot : Nat → Nat → reference.Scratch → Program Bytes State (Bool × reference.Scratch)) :
    List (Nat × Nat) → reference.Scratch → Program Bytes State (Bool × reference.Scratch)
  | [],s => .done (true,s)
  | (batch,kind)::rest,s => bind (slot batch kind s) fun out =>
      if out.1 then sequence slot rest out.2 else .done out

theorem sequence_eq (H : Bytes → State)
    (slot : Nat → Nat → reference.Scratch → Program Bytes State (Bool × reference.Scratch))
    (p : Parsed) (q : Fin 22 → Fin 262144) (nodes : Nat → Nat → Slice U8)
    (ss : List (Nat × Nat))
    (steps : ∀ b k, (b,k)∈ss → ∀ s, eval H (slot b k s)=
      eval H (MultiproofConeSlotState.slotState p q b k (nodes b k) s))
    (s : reference.Scratch) :
    eval H (sequence slot ss s)=eval H (MultiproofConeBatches.sequence p q nodes ss s) := by
  induction ss generalizing s with
  | nil => rfl
  | cons bk rest ih =>
    rcases bk with ⟨b,k⟩
    have head := steps b k (by simp) s
    simp only [sequence,MultiproofConeBatches.sequence,eval_bind,head]
    cases (eval H (MultiproofConeSlotState.slotState p q b k (nodes b k) s)).2 with
    | mk ok after =>
      cases ok with
      | false => rfl
      | true =>
        simp only [if_true]
        rw [ih (fun b k mem => steps b k (List.mem_cons_of_mem _ mem)) after]

#print axioms sequence_eq

def sourceBatch (occupied sibling : Parent) (leafSource : Leaf)
    (p : Parsed) (q : Fin 22 → Fin 262144) (nodes : Nat → Nat → Slice U8)
    (batch : Nat) (s : reference.Scratch) : Program Bytes State Bool :=
  bind (sequence (fun b k s => batch_tree (nodeWith occupied sibling) leafSource p q b k (nodes b k) s)
      [(batch,0),(batch,1),(batch,2)] s)
    (fun out => .done out.1)

theorem capacity_bound (b k : Nat) (hb : b<2) (hk : k<3) : capacity (3*b+k)≤172 := by
  interval_cases b <;> interval_cases k <;> decide

#print axioms capacity_bound

theorem slot_bound (p : Parsed) (nodes : Nat → Nat → Slice U8)
    (views : ∀ b k, b<2 → k<3 → MultiproofConeCanonical.bytesOf (nodes b k).val=
      slice p.wire (slotStart (3*b+k)) (32*capacity (3*b+k)))
    (b k : Nat) (hb : b<2) (hk : k<3) : (nodes b k).val.length≤5504 := by
  have len := congrArg List.length (views b k hb hk)
  have cap := capacity_bound b k hb hk
  simp only [MultiproofConeCanonical.bytesOf,List.length_map,slice,List.length_take,List.length_drop] at len
  omega

#print axioms slot_bound

theorem sourceBatch_eq {X : Type} (D : aspis_core.digest.Digest32 X) (hash : X)
    (H : Bytes → State) (binary occupied sibling : Parent) (leafSource : Leaf)
    (p6 : P6Boundary D hash H binary occupied sibling leafSource)
    (p : Parsed) (q : Fin 22 → Fin 262144) (nodes : Nat → Nat → Slice U8)
    (views : ∀ b k, b<2 → k<3 → MultiproofConeCanonical.bytesOf (nodes b k).val=
      slice p.wire (slotStart (3*b+k)) (32*capacity (3*b+k)))
    (batch : Nat) (hb : batch<2) (s : reference.Scratch) :
    eval H (sourceBatch occupied sibling leafSource p q nodes batch s)=
      eval H (MultiproofConeFrozen2Stage.sourceBatch p q nodes batch s) := by
  have sizes : ∀ b k, (b,k)∈[(batch,0),(batch,1),(batch,2)] → (nodes b k).val.length≤5504 := by
    intro b k mem
    simp only [List.mem_cons,List.not_mem_nil,or_false,Prod.mk.injEq] at mem
    rcases mem with ⟨hb',hk'⟩ | ⟨hb',hk'⟩ | ⟨hb',hk'⟩
    all_goals apply slot_bound p nodes views b k <;> omega
  have composed := sequence_eq H
    (fun b k s => batch_tree (nodeWith occupied sibling) leafSource p q b k (nodes b k) s)
    p q nodes [(batch,0),(batch,1),(batch,2)]
    (fun b k mem s => (function_certificates D hash H binary occupied sibling leafSource p6).2
      p q b k (nodes b k) (sizes b k mem) s) s
  simp only [sourceBatch,MultiproofConeFrozen2Stage.sourceBatch,MultiproofConeVerifyState.eval_map,composed]

#print axioms sourceBatch_eq

/-- Both frozen batches instantiated by the COMPOSED certificates. Only
the named LOCAL P6 boundary and S2/S10 physical/caller carrier binding
remain. Acceptance is the antecedent of the accepted-run statement; it is
not a precomputed whole-function certificate. Initial scratch is arbitrary. -/
theorem both_batches {X : Type} (D : aspis_core.digest.Digest32 X) (hash : X)
    (H : Bytes → State) (binary occupied sibling : Parent) (leafSource : Leaf)
    (p6 : P6Boundary D hash H binary occupied sibling leafSource)
    (p : Parsed) (q : Fin 22 → Fin 262144) (nodes : Nat → Nat → Slice U8)
    (views : ∀ b k, b<2 → k<3 → MultiproofConeCanonical.bytesOf (nodes b k).val=
      slice p.wire (slotStart (3*b+k)) (32*capacity (3*b+k))) :
    (∀ s, (eval H (sourceBatch occupied sibling leafSource p q nodes 0 s)).2=true →
      eval H (sourceBatch occupied sibling leafSource p q nodes 0 s)=
        eval H (OraclePortFrozen2.batch p q OraclePortFrozen2.batch0)) ∧
    (∀ s, (eval H (sourceBatch occupied sibling leafSource p q nodes 1 s)).2=true →
      eval H (sourceBatch occupied sibling leafSource p q nodes 1 s)=
        eval H (OraclePortFrozen2.batch p q OraclePortFrozen2.batch1)) := by
  have frozen := MultiproofConeFrozen2Stage.both_batches D hash H p6.oracle p q nodes views
  constructor
  · intro s accepted
    have composed := sourceBatch_eq D hash H binary occupied sibling leafSource p6 p q nodes views 0 (by decide) s
    rw [composed] at accepted ⊢
    exact frozen.1 s accepted
  · intro s accepted
    have composed := sourceBatch_eq D hash H binary occupied sibling leafSource p6 p q nodes views 1 (by decide) s
    rw [composed] at accepted ⊢
    exact frozen.2 s accepted

#print axioms both_batches
end AspisR1.MultiproofConeP6Frozen2Stage
end
