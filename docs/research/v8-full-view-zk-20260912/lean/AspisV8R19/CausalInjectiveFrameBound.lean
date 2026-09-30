import AspisV8R19.CausalTapeFirstHit
import AspisV8R19.UniformFrameCollision

/-! Causal first-hit loss for adaptive injective frames.

At step `i`, the frame and the list of prior addresses may depend on the
complete earlier tape prefix.  They cannot depend on the current or future
tape cells.  Pointwise injectivity then turns the fixed-prefix cardinality
bound into a complete-tape first-hit bound.  Instantiating the frames and
prior-read lists with an actual source callback remains separate. -/
set_option autoImplicit false
namespace AspisV8R19.CausalInjectiveFrameBound

open OracleResampling CausalFirstHitUnionBound CausalTapeFirstHit
open UniformFrameCollision

variable {S I : Type*} [Fintype S] [Nonempty S] [DecidableEq I]

def frameBad {n : Nat}
    (frame : (i : Fin n) → (Fin i.val → S) → S → I)
    (reads : (i : Fin n) → (Fin i.val → S) → List I)
    (i : Fin n) (history : Fin i.val → S) (s : S) : Prop :=
  frame i history s ∈ reads i history

theorem mean_frameBad_le {n : Nat}
    (frame : (i : Fin n) → (Fin i.val → S) → S → I)
    (reads : (i : Fin n) → (Fin i.val → S) → List I)
    (hinj : ∀ i history, Function.Injective (frame i history))
    (i : Fin n) (history : Fin i.val → S) :
    mean (fun s : S => indicator (frameBad frame reads i history s)) ≤
      ((reads i history).length : ℚ) / (Fintype.card S : ℚ) := by
  have heq : (fun s : S => indicator (frameBad frame reads i history s)) =
      hitIndicator (frame i history) (reads i history) := by
    funext s
    classical
    by_cases h : frame i history s ∈ reads i history <;>
      simp [indicator, frameBad, hitIndicator, h]
  rw [heq]
  exact mean_hitIndicator_list_le (frame i history) (reads i history)
    (hinj i history)

theorem causal_injective_frame_firstHit_le {n : Nat}
    (frame : (i : Fin n) → (Fin i.val → S) → S → I)
    (reads : (i : Fin n) → (Fin i.val → S) → List I)
    (limit : Fin n → Nat)
    (hinj : ∀ i history, Function.Injective (frame i history))
    (hlen : ∀ i history, (reads i history).length ≤ limit i) :
    mean (fun tape : Fin n → S => indicator (∃ i,
      event (frameBad frame reads) i tape)) ≤
      ∑ i, (limit i : ℚ) / (Fintype.card S : ℚ) := by
  apply mean_causal_firstHit_le (frameBad frame reads)
    (fun i => (limit i : ℚ) / (Fintype.card S : ℚ))
  intro i history
  exact (mean_frameBad_le frame reads hinj i history).trans
    (div_le_div_of_nonneg_right (by exact_mod_cast hlen i history) (by positivity))

#print axioms mean_frameBad_le
#print axioms causal_injective_frame_firstHit_le

end AspisV8R19.CausalInjectiveFrameBound
