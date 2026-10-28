import LPf_DotWordStep
import LPf_DotResidueStep
set_option autoImplicit false
namespace NBQ_DotBounds
open Aeneas Aeneas.Std
open AspisR1

def advance (s : U64) : List U64 → U64
  | [] => s
  | r::rs => advance (LPf_DotPushFour.update s r) rs

def rawSum : List U64 → Nat
  | [] => 0
  | r::rs => r.val + rawSum rs
/-- Aggregate bound and residue for every history, not only one wrapping step.
The history may have exactly4096 entries. All raw words are arbitrary. -/
theorem history (rs : List U64) (s : U64) (n : Nat)
    (hs : s.val ≤ n*LPf_DotWordStep.bound) (cap : n+rs.length≤4096) :
    (advance s rs).val ≤ (n+rs.length)*LPf_DotWordStep.bound ∧
    (advance s rs).val % 2147483647 = (s.val+rawSum rs) % 2147483647 := by
  induction rs generalizing s n with
  | nil => exact ⟨hs,by simp [advance,rawSum]⟩
  | cons r rs ih =>
    have hn : n<4096 := by simp only [List.length_cons] at cap; omega
    have step := LPf_DotWordStep.value s r n hn hs
    obtain ⟨bound,residue⟩ := ih (LPf_DotPushFour.update s r) (n+1) step.2 (by
      simp only [List.length_cons] at cap; omega)
    constructor
    · simpa only [advance,List.length_cons,Nat.add_assoc,Nat.add_comm,Nat.add_left_comm] using bound
    · change (advance (LPf_DotPushFour.update s r) rs).val % 2147483647 = _
      rw [residue,Nat.add_mod,LPf_DotResidueStep.source s r n hn hs]
      simp only [rawSum,Nat.add_mod,Nat.add_assoc,Nat.add_comm,Nat.add_left_comm,Nat.mod_mod]
/-- Reached per-coordinate histories from new fit well below u64 and reduce
exactly to the sum of raw residues. -/
theorem initial (rs : List U64) (cap : rs.length≤4096) :
    (advance 0#u64 rs).val ≤ rs.length*LPf_DotWordStep.bound ∧
    (advance 0#u64 rs).val % 2147483647 = rawSum rs % 2147483647 := by
  simpa using history rs 0#u64 0 (by simp) (by simpa using cap)
#print axioms history
#print axioms initial
end NBQ_DotBounds
