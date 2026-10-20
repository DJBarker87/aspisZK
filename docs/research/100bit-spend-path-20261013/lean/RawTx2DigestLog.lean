import RawDigestLogCarrier
import RawTx2ResumeDigestCalls

/-! Conditional stage-2 call inventory over the SAME byte carrier as tx1.
The site labels classify calls; caller reachability/coverage is a named premise.
External leaf and legacy parent boundaries must include their internal calls. -/
set_option autoImplicit false
noncomputable section
namespace AspisR1Stage2.Tx2DigestLog
open Aeneas Aeneas.Std Result
open AspisV8R19.DuplexFrames AspisR1DigestLogCarrier

inductive Site where
  | resumeProof | resumePublic | resumeChecksum
  | siblingLeft | siblingRight | occupiedParent
  | privateLeafBoundary | legacyParentBoundary | runtimeBoundary

structure Call {H : Type} (D : aspis_core.digest.Digest32 H) where
  site : Site
  hash : H
  input : Slice (Slice U8)
  output : Array U8 32#usize
  success : D.digest hash input = ok output

def pair {H : Type} {D : aspis_core.digest.Digest32 H} (c : Call D) : Bytes × State :=
  (flatten c.input, decodeState c.output)

def ActualPair {H : Type} (D : aspis_core.digest.Digest32 H) (q : Bytes × State) : Prop :=
  ∃ (hash : H) (input : Slice (Slice U8)) (output : Array U8 32#usize),
    q = (flatten input, decodeState output) ∧ D.digest hash input = ok output

/-- One ROM interface shared with tx1, not a law of the Digest32 signature. -/
def ByteOracleBackend {H : Type} (D : aspis_core.digest.Digest32 H)
    (Hbytes : Bytes → State) : Prop := ∀ q, ActualPair D q → q.2 = Hbytes q.1

def resumeCalls {H : Type} {D : aspis_core.digest.Digest32 H}
    {hash : H} {bytes proof public1 : Slice U8}
    (c : Tx2ResumeDigests.Calls D hash bytes proof public1) : List (Call D) :=
  [{site := .resumeProof, hash, input := c.proofParts, output := c.proofDigest,
      success := c.proofCall},
   {site := .resumePublic, hash, input := c.publicParts, output := c.publicDigest,
      success := c.publicCall},
   {site := .resumeChecksum, hash, input := c.checksumParts, output := c.checksumDigest,
      success := c.checksumCall}]

/-- Inventory, retaining repetitions; not an ordered execution or first-read log.
Remaining calls include every Merkle/backend/runtime call reached by tx2. -/
def log {H : Type} {D : aspis_core.digest.Digest32 H}
    {hash : H} {bytes proof public1 : Slice U8}
    (c : Tx2ResumeDigests.Calls D hash bytes proof public1)
    (remaining : List (Call D)) : List (Bytes × State) :=
  (resumeCalls c ++ remaining).map pair

/-- Requires an actual execution trace, including opaque/external callee calls. -/
def Tx2InventoryComplete (reached : Bytes × State → Prop)
    (tr : List (Bytes × State)) : Prop := ∀ q, reached q → q ∈ tr

theorem log_actual {H : Type} {D : aspis_core.digest.Digest32 H}
    {hash : H} {bytes proof public1 : Slice U8}
    (c : Tx2ResumeDigests.Calls D hash bytes proof public1) (rest : List (Call D)) :
    ∀ q ∈ log c rest, ActualPair D q := by
  intro q hq
  obtain ⟨call, _, rfl⟩ := List.mem_map.mp hq
  exact ⟨call.hash,call.input,call.output,rfl,call.success⟩

theorem log_consistent {H : Type} {D : aspis_core.digest.Digest32 H}
    {hash : H} {bytes proof public1 : Slice U8}
    (c : Tx2ResumeDigests.Calls D hash bytes proof public1) (rest : List (Call D))
    (Hbytes : Bytes → State) (backend : ByteOracleBackend D Hbytes) :
    ∀ q ∈ log c rest, q.2 = Hbytes q.1 := by
  intro q hq
  exact backend q (log_actual c rest q hq)

theorem resume_contained {H : Type} {D : aspis_core.digest.Digest32 H}
    {hash : H} {bytes proof public1 : Slice U8}
    (c : Tx2ResumeDigests.Calls D hash bytes proof public1) (rest : List (Call D)) :
    (resumeCalls c).map pair ⊆ log c rest := by
  intro q hq
  obtain ⟨call,hc,rfl⟩ := List.mem_map.mp hq
  exact List.mem_map.mpr ⟨call,List.mem_append_left _ hc,rfl⟩

theorem every_reached_call {H : Type} {D : aspis_core.digest.Digest32 H}
    {hash : H} {bytes proof public1 : Slice U8}
    (c : Tx2ResumeDigests.Calls D hash bytes proof public1) (rest : List (Call D))
    (Hbytes : Bytes → State) (backend : ByteOracleBackend D Hbytes)
    (reached : Bytes × State → Prop) (coverage : Tx2InventoryComplete reached (log c rest)) :
    ∀ q, reached q → q ∈ log c rest ∧ q.2 = Hbytes q.1 := by
  intro q hq
  exact ⟨coverage q hq,log_consistent c rest Hbytes backend q (coverage q hq)⟩

#print axioms log_actual
#print axioms log_consistent
#print axioms resume_contained
#print axioms every_reached_call
end AspisR1Stage2.Tx2DigestLog
end
