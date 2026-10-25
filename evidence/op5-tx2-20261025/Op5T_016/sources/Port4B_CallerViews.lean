import S2LeadInterface

set_option autoImplicit false
noncomputable section
namespace AspisR1.Port4B_CallerViews
open Aeneas Aeneas.Std Result AspisR1Stage2
open AspisV8R19.DuplexFrames AspisV8R19.SourceDuplexStep
open OraclePortCompactDraft OraclePortSelectedDraft
open AspisV8R19.MemoizedProgramLaw AspisV8R19.OracleProgramOps
open S2LeadInterface

/-- All six admitted physical node buffers and their length bounds come from
Required14, without separately assuming a slot view or exact length. -/
theorem physical_views {Observer Hash : Type} (c : Inputs Observer)
    (D : aspis_core.digest.Digest32 Hash) (hash : Hash) (H : Bytes → State)
    (stored pub saved : Bytes) (parsed : Parsed)
    (facts : S2CallerFacts c D hash H stored pub saved parsed) :
    ∀ b k, b < 2 → k < 3 →
      MultiproofConeCanonical.bytesOf (c.nodes b k).val =
        slice parsed.wire (slotStart (3*b+k)) (32*capacity (3*b+k)) ∧
      (c.nodes b k).val.length ≤ 5504 := by
  intro b k hb hk
  exact ⟨facts.nodeViews b k hb hk,
    MultiproofConeP6Frozen2Stage.slot_bound parsed c.nodes facts.nodeViews b k hb hk⟩

/-- Instantiate the local named P6 boundary's oracle field with the SAME
caller's digest dictionary. Parent/leaf gates remain explicit and unchanged. -/
theorem callerP6 {Observer Hash : Type} (c : Inputs Observer)
    (D : aspis_core.digest.Digest32 Hash) (hash : Hash) (H : Bytes → State)
    (stored pub saved : Bytes) (parsed : Parsed)
    (facts : S2CallerFacts c D hash H stored pub saved parsed)
    (binary occupied sibling : MultiproofConeP6Callbacks.Parent)
    (leaf : MultiproofConeP6Batch.Leaf)
    (p6 : MultiproofConeP6Frozen2Stage.P6Boundary (multiproofDigest D) hash H binary occupied sibling leaf) :
    MultiproofConeP6Frozen2Stage.P6Boundary (multiproofDigest D) hash H binary occupied sibling leaf :=
  {p6 with oracle := facts.oracle}

/-- Exact log-and-return observation transport of the P6 sourceBatch to its
frozen source on BOTH row indices, before any acceptance restriction.
This says sourceBatch, never the installed native op5. -/
theorem source_rows {Observer Hash : Type} (c : Inputs Observer)
    (D : aspis_core.digest.Digest32 Hash) (hash : Hash) (H : Bytes → State)
    (stored pub saved : Bytes) (parsed : Parsed)
    (facts : S2CallerFacts c D hash H stored pub saved parsed)
    (binary occupied sibling : MultiproofConeP6Callbacks.Parent)
    (leaf : MultiproofConeP6Batch.Leaf)
    (p6 : MultiproofConeP6Frozen2Stage.P6Boundary (multiproofDigest D) hash H binary occupied sibling leaf)
    (q : Fin 22 → Fin 262144) :
    ∀ b, b < 2 → ∀ s,
      eval H (MultiproofConeP6Frozen2Stage.sourceBatch occupied sibling leaf parsed q c.nodes b s) =
      eval H (MultiproofConeFrozen2Stage.sourceBatch parsed q c.nodes b s) := by
  intro b hb s
  exact MultiproofConeP6Frozen2Stage.sourceBatch_eq (multiproofDigest D) hash H binary occupied sibling leaf
    (callerP6 c D hash H stored pub saved parsed facts binary occupied sibling leaf p6)
    parsed q c.nodes facts.nodeViews b hb s

#print axioms callerP6
#print axioms physical_views
#print axioms source_rows
end AspisR1.Port4B_CallerViews
end
