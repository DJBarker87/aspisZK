import NBE_Audit
import NBI_Audit
import Port4B_Opening

set_option autoImplicit false
namespace AspisR1.NBJ_Opening
open Aeneas Aeneas.Std Result
open AspisV8R19.DuplexFrames

/-- Scalar endpoints checked independently of the physical byte carrier. -/
def start (i : Nat) : Nat := 10055 + i * 832
def finish (i : Nat) : Nat := start i + 832

theorem address_bounds (i : Nat) (bound : i < 22) :
    start i ≤ finish i ∧ finish i ≤ 57607 ∧ finish i - start i = 832 := by
  unfold finish start
  omega

/-- Consume the existing checked physical reader and leaf bridge on the same
proof, selected index, digest reply and chronological prefix. -/
theorem selected_leaf {X : Type} (D : AspisR1Stage2.aspis_core.digest.Digest32 X)
    (hash : X) (proof : Slice U8) (len : proof.val.length = 57607)
    (i kind : Usize) (bound : i.val < 22) (before : CheckpointBytes5Effect.Log) :
    ∃ view, Port4B_Opening.opening proof i = ok view ∧ view.val.length = 832 ∧
      MultiproofConeCanonical.bytesOf view.val = OraclePortCompactDraft.slice
        (MultiproofConeCanonical.bytesOf proof.val) (start i.val) 832 ∧
      CheckpointBytes5Effect.run D hash (Port4B_LeafCode.code kind view) before =
        (do let digest ← D.digest hash (Port4B_LeafCode.input kind view)
            ok (digest,before++[(Port4B_LeafCode.input kind view,digest)])) := by
  exact NBI_Views.opening_leaf D hash proof len i kind bound before

#print axioms address_bounds
#print axioms selected_leaf
end AspisR1.NBJ_Opening
