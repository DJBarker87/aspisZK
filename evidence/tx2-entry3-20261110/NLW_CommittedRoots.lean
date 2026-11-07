import NLW_DigestBoundary
set_option autoImplicit false
noncomputable section
namespace NLW_CommittedRoots
open Aeneas Aeneas.Std AspisR1
open AspisV8R19.SqueezeOracleBridge
/-- The second semantic root is row2's payload:16-byte proof header,
32-byte c1 root,and three5-byte record headers. Rows0/1 have empty payloads;
compaction affects rows>=14 only. Native source pins are recorded separately. -/
def proofRoot (proof : Slice U8) (offset : Nat) : List U8 :=
 (encodeState ((SemanticRecordCodec.decodeState (OraclePortCompactDraft.slice
 (MultiproofConeCanonical.bytesOf proof.val) offset 32)).getD (fun _=>0))).val
def Root1 (checkpoint proof : Slice U8) : Prop :=
 (checkpoint.val.drop 144).take 32=proofRoot proof 63
/-- Required caller provenance includes BOTH committed roots. The sibling
callee's narrower Root0 clause is only its first projection; a local Parsed
root1 witness is not proof of the original wire's second commitment. -/
def Both (checkpoint proof : Slice U8) : Prop :=
 NLW_Root0.Binds checkpoint proof ∧ Root1 checkpoint proof
theorem second_offset : 16+32+5+5+5=63 := rfl
theorem first (checkpoint proof : Slice U8) (both : Both checkpoint proof) :
 NLW_Root0.Binds checkpoint proof := both.1
/-- Hash realization is not injectivity: both-root transport retains a
concrete collision alternative,without adding a no-collision hypothesis. -/
theorem both_or_collision {D : Type} (hash : List U8 → D)
 (checkpoint oldProof proof : Slice U8) (saved : Both checkpoint oldProof)
 (checked : hash oldProof.val=hash proof.val) :
 Both checkpoint proof ∨ NLW_DigestBoundary.Collision hash oldProof proof := by
 by_cases roots : Both checkpoint proof
 · exact .inl roots
 · apply Or.inr
   refine ⟨?_,checked⟩
   intro same
   apply roots
   simpa only [Both,Root1,proofRoot,NLW_Root0.Binds,same] using saved
#print Both
#print Root1
#print second_offset
#print first
#print both_or_collision
#print axioms second_offset
#print axioms first
#print axioms both_or_collision
end NLW_CommittedRoots
