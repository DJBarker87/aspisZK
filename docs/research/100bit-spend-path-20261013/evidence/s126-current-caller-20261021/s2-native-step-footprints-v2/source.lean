import Lean.Elab.Tactic.Omega
set_option autoImplicit false

namespace AspisS2NativeStepFootprints

/-- Full byte-memory observations. This is a projection of actual memory,
not an SDK or guard carrier used to replace source execution. -/
abbrev Heap (Byte : Type) := Nat → Byte

def Span (base size address : Nat) : Prop := base ≤ address ∧ address < base + size

def Frame {Byte : Type} (before after : Heap Byte) (allowed : Nat → Prop) : Prop :=
  ∀ address, ¬ allowed address → after address = before address

def View {Byte : Type} (memory : Heap Byte) (base size : Nat) : Fin size → Byte :=
  fun index => memory (base + index.val)

theorem frame_trans {Byte : Type} (before middle after : Heap Byte)
    (left right : Nat → Prop)
    (first : Frame before middle left) (second : Frame middle after right) :
    Frame before after (fun address => left address ∨ right address) := by
  intro address outside
  rw [second address (fun h => outside (Or.inr h)),
    first address (fun h => outside (Or.inl h))]

theorem view_frame {Byte : Type} (before after : Heap Byte)
    (allowed : Nat → Prop) (base size : Nat)
    (frame : Frame before after allowed)
    (separate : ∀ address, Span base size address → ¬ allowed address) :
    View after base size = View before base size := by
  funext index
  exact frame (base + index.val) (separate _ ⟨by omega,by have h := index.isLt;omega⟩)

/-- An arbitrary finite sequence of checked source steps. Composition does not
unfold any concrete payload or require a whole-buffer symbolic observation. -/
theorem sequence_frame {Byte : Type} (n : Nat) (states : Nat → Heap Byte)
    (allowed : Nat → Prop)
    (steps : ∀ i, i < n → Frame (states i) (states (i+1)) allowed) :
    Frame (states 0) (states n) allowed := by
  induction n with
  | zero => intro address _;rfl
  | succ n ih =>
    have hprefix := ih (fun i hi => steps i (by omega))
    intro address outside
    rw [steps n (by omega) address outside,hprefix address outside]

/-- Exact rule needed after the native copy: its destination is the only
byte-array write; cleanup permits only actual counter cells. The concrete
copy/cleanup source certificates and call-site separation must instantiate
these premises. This theorem alone is not actual-source correspondence. -/
theorem copy_cleanup_other_view {Byte : Type} (before copied out : Heap Byte)
    (checkpoint counters : Nat → Prop) (base size : Nat)
    (copy : Frame before copied checkpoint)
    (cleanup : Frame copied out counters)
    (separate : ∀ address, Span base size address →
      ¬ checkpoint address ∧ ¬ counters address) :
    View out base size = View before base size := by
  apply view_frame before out _ base size (frame_trans _ _ _ _ _ copy cleanup)
  intro address valid
  obtain ⟨cp,flag⟩ := separate address valid
  exact fun h => h.elim cp flag

/-- Cleanup cannot change the checkpoint bytes established by the actual
whole-copy certificate, even though it updates borrow counters. -/
theorem copy_cleanup_saved_view {Byte : Type} (copied out : Heap Byte)
    (counters : Nat → Prop) (base size : Nat) (checkpoint : Fin size → Byte)
    (saved : View copied base size = checkpoint)
    (cleanup : Frame copied out counters)
    (separate : ∀ address, Span base size address → ¬ counters address) :
    View out base size = checkpoint :=
  (view_frame copied out counters base size cleanup separate).trans saved

#print axioms frame_trans
#print axioms view_frame
#print axioms sequence_frame
#print axioms copy_cleanup_other_view
#print axioms copy_cleanup_saved_view
end AspisS2NativeStepFootprints
