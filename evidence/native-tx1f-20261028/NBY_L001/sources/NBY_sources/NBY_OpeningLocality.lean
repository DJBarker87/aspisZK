import NBV_Audit
import NBJ_WindowCover

set_option autoImplicit false
namespace AspisR1.NBY_OpeningLocality
open NBJ_WindowCover

/-- Reborrowing an indexed window preserves its absolute read coordinate.
The carrier is arbitrary; no independent memory or byte-equality premise. -/
theorem reborrow {α : Type} (memory : Nat → α) (base offset width : Nat) :
    image (fun k => memory (base+k)) offset width =
      image memory (base+offset) width := by
  unfold image
  congr 1
  funext k
  simp only [Nat.add_assoc]

/-- Combine the installed opening pointer with the small indexed-load law
on that SAME carrier. This is a value law, not a native pointer theorem. -/
theorem opening_window {α : Type} (memory : Nat → α) (i w : Nat) :
    image (fun k => memory (10055+832*i+k)) (32*w) 32 =
      image memory (10055+832*i+32*w) 32 :=
  reborrow memory (10055+832*i) (32*w) 32

/-- Local reads of all twenty-six windows determine the whole read image.
Only the inherited cover theorem is used, with rebased coordinates. -/
theorem opening_loads {α : Type} (memory : Nat → α) (read : Nat → α) (i : Nat)
    (loads : ∀ w, w < 26 → ∀ c, c < 32 →
      read (32*w+c) = memory (10055+832*i+32*w+c)) :
    image read 0 832 = image memory (10055+832*i) 832 := by
  rw [← NBJ_WindowCover.relocation memory (10055+832*i) 832]
  apply NBJ_WindowCover.opening_cover
  intro w hw c hc
  simpa only [Nat.zero_add, Nat.add_assoc] using loads w hw c hc

#print axioms reborrow
#print axioms opening_window
#print axioms opening_loads
end AspisR1.NBY_OpeningLocality
