import PV_L1G_WorldRetry
set_option autoImplicit false
namespace PV_L1G_WorldRetry
open R1Z.PV_W_Threading
variable {W S P : Type}
/-- Reach is driven by the actual full-world leaf and its normal retry edge.
There is no reach edge after success, ordinary error, outer failure or div. -/
inductive Reach (a : Attempt W S P) (start : Nat) (initial : S) (world : W) : Nat → S → W → Prop
 | initial : Reach a start initial world start initial world
 | retry {k : Nat} {s after : S} {w : W} : Reach a start initial world k s w →
   (a k s w).outcome = .ok (.retry,after) →
   Reach a start initial world (k+1) after (a k s w).world
/-- Reached leaf equality suffices for the entire ordered world run, including
failed and divergent prefixes. No totality or success-only restriction. -/
theorem reached_congr (a b : Attempt W S P) (start : Nat) (initial : S) (world : W)
 (leaves : ∀ k s w, Reach a start initial world k s w → a k s w = b k s w)
 (n k : Nat) (s : S) (w : W) (reached : Reach a start initial world k s w) :
 run a n k s w = run b n k s w := by
 induction n generalizing k s w with
 | zero => rfl
 | succ n ih =>
   have same := leaves k s w reached
   cases h : (a k s w).outcome with
   | fail e => simp only [run,R1Z.PV_W_Threading.bind,← same,h]
   | div => simp only [run,R1Z.PV_W_Threading.bind,← same,h]
   | ok pair =>
     rcases pair with ⟨out,after⟩
     cases out with
     | done p => simp only [run,R1Z.PV_W_Threading.bind,← same,h]
     | stop e => simp only [run,R1Z.PV_W_Threading.bind,← same,h]
     | retry =>
       have rest := ih (k+1) after (a k s w).world (.retry reached h)
       simp only [run,R1Z.PV_W_Threading.bind,← same,h,rest]
#print axioms reached_congr
end PV_L1G_WorldRetry
