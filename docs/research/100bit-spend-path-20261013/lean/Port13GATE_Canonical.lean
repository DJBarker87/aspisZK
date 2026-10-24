import MultiproofConeP6Frozen2Stage

set_option autoImplicit false
noncomputable section
namespace AspisR1.Port13GATE_Canonical
open Aeneas Aeneas.Std Result
open AspisV8R19.DuplexFrames AspisV8R19.SourceDuplexStep
open AspisV8R19.MemoizedProgramLaw AspisV8R19.OracleProgramOps
open MultiproofConeP6Callbacks MultiproofConeP6Batch MultiproofConePhysicalTransport

/-- A mathematical witness for the canonical comparison only. It is not
installed in, sampled by, or substituted into any source experiment. -/
def dictionary (H : Bytes → State) : MultiproofConeRef.aspis_core.digest.Digest32 Unit where
  coremarkerCopyInst := {cloneInst := {clone := fun q => ok q}}
  digest := fun _ input => ok (rawOracle H input)

/-- The formerly required total law is constructed for the proof dictionary.
The unused binary callback is occupied; no binary callback premise is needed. -/
theorem boundary (H : Bytes → State) (occupied sibling : Parent) (leaf : Leaf)
    (occupiedGate : ParentGate (rawOracle H) occupied)
    (siblingGate : ParentGate (rawOracle H) sibling) (leafGate : LeafGate H leaf) :
    MultiproofConeP6Frozen2Stage.P6Boundary (dictionary H) () H occupied occupied sibling leaf :=
  ⟨fun _ => rfl,occupiedGate,occupiedGate,siblingGate,leafGate⟩

/-- Both Programs in this concrete comparison are independent of the digest
parameter. H and all actual callback Programs are preserved. -/
theorem both_batches (H : Bytes → State) (occupied sibling : Parent) (leaf : Leaf)
    (occupiedGate : ParentGate (rawOracle H) occupied)
    (siblingGate : ParentGate (rawOracle H) sibling) (leafGate : LeafGate H leaf)
    (p : OraclePortCompactDraft.Parsed) (q : Fin 22 → Fin 262144)
    (nodes : Nat → Nat → Slice U8)
    (views : ∀ b k, b<2 → k<3 → MultiproofConeCanonical.bytesOf (nodes b k).val=
      OraclePortCompactDraft.slice p.wire (OraclePortSelectedDraft.slotStart (3*b+k))
        (32*OraclePortSelectedDraft.capacity (3*b+k))) :
    (∀ s, (eval H (MultiproofConeP6Frozen2Stage.sourceBatch occupied sibling leaf p q nodes 0 s)).2=true →
      eval H (MultiproofConeP6Frozen2Stage.sourceBatch occupied sibling leaf p q nodes 0 s)=
        eval H (OraclePortFrozen2.batch p q OraclePortFrozen2.batch0)) ∧
    (∀ s, (eval H (MultiproofConeP6Frozen2Stage.sourceBatch occupied sibling leaf p q nodes 1 s)).2=true →
      eval H (MultiproofConeP6Frozen2Stage.sourceBatch occupied sibling leaf p q nodes 1 s)=
        eval H (OraclePortFrozen2.batch p q OraclePortFrozen2.batch1)) :=
  MultiproofConeP6Frozen2Stage.both_batches (dictionary H) () H occupied occupied sibling leaf
    (boundary H occupied sibling leaf occupiedGate siblingGate leafGate) p q nodes views

#print axioms boundary
#print axioms both_batches
end AspisR1.Port13GATE_Canonical
end
