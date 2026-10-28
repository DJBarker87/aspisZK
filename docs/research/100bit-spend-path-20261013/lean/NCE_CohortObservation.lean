import NCE_FirstFailure

set_option autoImplicit false
noncomputable section
namespace AspisR1.NCE_CohortObservation
open Aeneas Aeneas.Std Result MultiproofConeRef NCE_FirstFailure
open AspisV8R19.DuplexFrames AspisV8R19.SourceDuplexStep
open AspisV8R19.MemoizedProgramLaw AspisV8R19.OracleProgramOps

/-- Congruence for the NEW first-failed-tree observation. The main theorem
below derives each slot equality from existing local P6 gates; no native
whole-tree equality is hypothesized there. -/
theorem observe_congr (H : Bytes → State) (left right : Slot)
    (ss : List (Nat × Nat))
    (steps : ∀ b k, (b,k) ∈ ss → ∀ s, eval H (left b k s) = eval H (right b k s))
    (s : reference.Scratch) : observe H left ss s = observe H right ss s := by
  induction ss generalizing s with
  | nil => rfl
  | cons bk rest ih =>
    rcases bk with ⟨b,k⟩
    simp only [observe,steps b k (List.mem_cons_self) s]
    split
    next accepted =>
      rw [ih (fun b k mem => steps b k (List.mem_cons_of_mem _ mem))]
    next rejected => rfl

/-- Same Parsed/proof-node views, queries and arbitrary initial scratch.
The first failed tree, every attempted digest read and final scratch agree
between the P6 cohort and its owned physical model on ALL outcomes. This
consumes the existing local leaf/node contracts, not a successful batch fact.
It remains a MODEL theorem until the separate native/control cuts are bound. -/
theorem three_trees {X : Type} (D : aspis_core.digest.Digest32 X) (hash : X)
    (H : Bytes → State) (binary occupied sibling : MultiproofConeP6Callbacks.Parent)
    (leaf : MultiproofConeP6Batch.Leaf)
    (p6 : MultiproofConeP6Frozen2Stage.P6Boundary D hash H binary occupied sibling leaf)
    (p : OraclePortCompactDraft.Parsed) (q : Fin 22 → Fin 262144)
    (nodes : Nat → Nat → Slice U8)
    (views : ∀ b k, b < 2 → k < 3 → MultiproofConeCanonical.bytesOf (nodes b k).val =
      OraclePortCompactDraft.slice p.wire (OraclePortSelectedDraft.slotStart (3*b+k))
        (32*OraclePortSelectedDraft.capacity (3*b+k)))
    (b : Nat) (batch : b < 2) (s : reference.Scratch) :
    observe H (fun b k s => MultiproofConeP6Batch.batch_tree
      (MultiproofConeP6Callbacks.nodeWith occupied sibling) leaf p q b k (nodes b k) s)
      [(b,0),(b,1),(b,2)] s =
    observe H (fun b k s => MultiproofConeSlotState.slotState p q b k (nodes b k) s)
      [(b,0),(b,1),(b,2)] s := by
  apply observe_congr
  intro bb k mem after
  have bounds : bb < 2 ∧ k < 3 := by
    simp only [List.mem_cons,List.not_mem_nil,or_false,Prod.mk.injEq] at mem
    rcases mem with ⟨rfl,rfl⟩ | ⟨rfl,rfl⟩ | ⟨rfl,rfl⟩ <;> omega
  exact (MultiproofConeP6Frozen2Stage.function_certificates
    D hash H binary occupied sibling leaf p6).2 p q bb k (nodes bb k)
      (MultiproofConeP6Frozen2Stage.slot_bound p nodes views bb k bounds.1 bounds.2) after

/-- The existing cohort's batch result is the success projection of the SAME
owned first-failure observation. This is exact for rejected prefixes as well
as acceptance, with no equality of Rust error enums asserted. -/
theorem batch_result {X : Type} (D : aspis_core.digest.Digest32 X) (hash : X)
    (H : Bytes → State) (binary occupied sibling : MultiproofConeP6Callbacks.Parent)
    (leaf : MultiproofConeP6Batch.Leaf)
    (p6 : MultiproofConeP6Frozen2Stage.P6Boundary D hash H binary occupied sibling leaf)
    (p : OraclePortCompactDraft.Parsed) (q : Fin 22 → Fin 262144)
    (nodes : Nat → Nat → Slice U8)
    (views : ∀ b k, b < 2 → k < 3 → MultiproofConeCanonical.bytesOf (nodes b k).val =
      OraclePortCompactDraft.slice p.wire (OraclePortSelectedDraft.slotStart (3*b+k))
        (32*OraclePortSelectedDraft.capacity (3*b+k)))
    (b : Nat) (batch : b < 2) (s : reference.Scratch) :
    eval H (MultiproofConeP6Frozen2Stage.sourceBatch occupied sibling leaf p q nodes b s) =
      let out := observe H (fun b k s => MultiproofConeSlotState.slotState p q b k (nodes b k) s)
        [(b,0),(b,1),(b,2)] s
      (out.1,out.2.1.isNone) := by
  rw [NCE_FirstFailure.batch_observation,
    three_trees D hash H binary occupied sibling leaf p6 p q nodes views b batch s]

#print axioms observe_congr
#print axioms three_trees
#print axioms batch_result
end AspisR1.NCE_CohortObservation
end
