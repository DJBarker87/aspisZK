import NJM_CircleNative
import NJM_RoundStage
set_option autoImplicit false
namespace AspisR1.NJM_ChildDomain
open Aeneas Aeneas.Std Result AspisR1PublicPreparation

/-- The native semantic/block cut accepts exactly success or RowOrder; outer
failure and divergence remain separate abort prefixes. -/
def Good {A H : Type} (reply : Result (core.result.Result A r1_wire.Error × r1_wire.SemanticTranscript H)) : Prop :=
 match reply with
 | .ok (.Ok _,_) => True
 | .ok (.Err (.RowOrder _ _),_) => True
 | .ok (.Err _,_) => False
 | .fail _ => True
 | .div => True

theorem bind_good {A B H : Type} (reply : Result A)
 (next : A→Result (core.result.Result B r1_wire.Error × r1_wire.SemanticTranscript H))
 (good : ∀ a,Good (next a)) : Good (reply >>= next) := by
 cases reply with
 | ok a => exact good a
 | fail e => trivial
 | div => trivial

/-- No digest value law or success assumption: every original outer abort
is preserved and the only Rust error is the exact RowOrder pair. -/
theorem block {H : Type} (D : aspis_core.Digest32 H) (t : r1_wire.SemanticTranscript H)
 (row : U8) (framed : Slice U8) :
 Good (r1_wire.SemanticTranscript.sample_block_validated D t row framed) := by
 unfold r1_wire.SemanticTranscript.sample_block_validated
 split
 · trivial
 · repeat' first
    | (apply bind_good;intro value)
    | (solve | trivial)

/-- Every returning child reply satisfies the native domain at the SAME call. -/
theorem block_reply {H : Type} (D : aspis_core.Digest32 H) (t after : r1_wire.SemanticTranscript H)
 (row : U8) (framed : Slice U8) (reply : NIX_DispatchCut.Reply)
 (call : r1_wire.SemanticTranscript.sample_block_validated D t row framed=ok (reply,after)) :
 NIX_DispatchCut.childDomain reply := by
 have good:=block D t row framed
 rw [call] at good
 cases reply with
 | Ok b => trivial
 | Err error => cases error <;> exact good

#print axioms bind_good
#print axioms block
#print axioms block_reply
end AspisR1.NJM_ChildDomain
