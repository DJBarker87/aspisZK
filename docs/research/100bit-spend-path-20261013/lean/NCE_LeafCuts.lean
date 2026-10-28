import NCE_OpeningRead
import Port4B_LeafCut

set_option autoImplicit false
noncomputable section
namespace AspisR1.NCE_LeafCuts
open Aeneas Aeneas.Std Result ControlFlow MultiproofConeRef NCE_OpeningCuts
open CheckpointBytes5Effect Port4B_LeafStep
open AspisV8R19.DuplexFrames AspisV8R19.SourceDuplexStep
open AspisV8R19.SqueezeOracleBridge

abbrev Request := Usize → Slice U8 → Code CheckpointBytes5Effect.Digest
abbrev Post := Carrier → U32 → CheckpointBytes5Effect.Digest → Usize →
  Result (ControlFlow LoopState LoopOut × Carrier)

/-- The actual post-hash scratch return, inside the SAME caller context.
Duplicate failure returns its actual current scratch; no suffix is invented. -/
def returnedCarrier (s : Carrier) : ControlFlow LoopState LoopOut → Carrier
  | .cont (idx,val,n,_) => {s with scratch:={s.scratch with idx:=idx,val:=val,n:=n}}
  | .done (idx,val,_) => {s with scratch:={s.scratch with idx:=idx,val:=val}}

/-- Two phase-selected ONE-step facts for the leaf member: one actual hash
request/reply and one actual post-hash duplicate/new/error continuation.
No whole traversal, selected-opening success or final accepted tree is assumed.
The request law retains every raw prefix and the post law frames the full
caller. Their raw/high-level log binding is a separate remaining join. -/
def NCE_Native_Leaf (request : Request) (post : Post) : Prop :=
  (∀ {X : Type} (D : AspisR1Stage2.aspis_core.digest.Digest32 X) (hash : X)
      (kind : Usize) (view : Slice U8) (before : CheckpointBytes5Effect.Log),
      kind.val < 3 → view.val.length = 832 →
      run D hash (request kind view) before = run D hash (Port4B_LeafCode.code kind view) before) ∧
  (∀ (s : Carrier) (index : U32) (reply : CheckpointBytes5Effect.Digest) (pos : Usize),
      s.scratch.n.val < 16 →
      post s index reply pos = (do
        let out ← Port4B_LeafStep.post s.scratch.idx s.scratch.val s.scratch.n index reply pos
        ok (out,returnedCarrier s out)))

/-- The syscall value is the existing runtime trust law. The native cut only
binds exact slices and the unchanged reply, never a SHA implementation. -/
theorem request_observation (request : Request) (post : Post)
    (cut : NCE_Native_Leaf request post) {X : Type}
    (D : AspisR1Stage2.aspis_core.digest.Digest32 X) (hash : X) (H : Bytes → State)
    (law : ∀ input, D.digest hash input = ok (MultiproofConePhysicalTransport.rawOracle H input))
    (kind : Usize) (view : Slice U8) (before : CheckpointBytes5Effect.Log)
    (kb : kind.val < 3) (size : view.val.length = 832) :
    run D hash (request kind view) before =
      ok (encodeState (H (flatten (Port4B_LeafCode.input kind view))),
        before++[(Port4B_LeafCode.input kind view,
          encodeState (H (flatten (Port4B_LeafCode.input kind view))))]) := by
  rw [cut.1 D hash kind view before kb size]
  exact (Port4B_LeafCode.native_and_reads D hash H law kind view size before).2

/-- The exact actual reply is passed to the inherited post-hash model. This
covers duplicate success, duplicate mismatch and insertion with arbitrary
scratch suffix; it does not assume that the selected leaf was accepted. -/
theorem post_association (request : Request) (post : Post)
    (cut : NCE_Native_Leaf request post) (s : Carrier) (index : U32)
    (reply : CheckpointBytes5Effect.Digest) (pos : Usize) (room : s.scratch.n.val < 16) :
    post s index reply pos =
      let out := project s.scratch pos (MultiproofConeLeafContent.next s.scratch index reply room)
      ok (out,returnedCarrier s out) := by
  rw [cut.2 s index reply pos room,Port4B_LeafStep.post_exact s.scratch index reply pos room]
  rfl

/-- Post-control preserves the SAME external caller fields even on duplicate
failure. Scratch is intentionally carried separately from accepted values. -/
theorem post_frame (s : Carrier) (out : ControlFlow LoopState LoopOut) :
    (returnedCarrier s out).prepared = s.prepared ∧
    (returnedCarrier s out).proof = s.proof ∧
    (returnedCarrier s out).log = s.log := by
  cases out with
  | cont state => rcases state with ⟨idx,val,n,pos⟩; exact ⟨rfl,rfl,rfl⟩
  | done state => rcases state with ⟨idx,val,pending⟩; exact ⟨rfl,rfl,rfl⟩

#print axioms request_observation
#print axioms post_association
#print axioms post_frame
end AspisR1.NCE_LeafCuts
end
