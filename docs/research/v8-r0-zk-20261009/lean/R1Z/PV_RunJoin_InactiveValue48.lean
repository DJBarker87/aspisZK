import R1Z.PV_RunJoin_InactiveValueCell48
import R1Z.PV_RunJoin_InactiveFinite48
set_option autoImplicit false
noncomputable section
namespace R1Z.PV_RunJoin_InactiveValue48
open Aeneas Aeneas.Std Result
open ProverCommitWideOps48
open PV_RunJoin_InactiveValueCell48 (input)

def total (q : Nat → Raw) : Nat → Nat → Exact
  | 0,_ => 0
  | n+1,i => value (q i)*PV_RunJoin_InactiveIndicator48.mask i+total q n (i+1)

attribute [local irreducible] source value total

theorem complete (q : Nat → Raw) (hq : ∀ j,j<1024 → canonical (q j))
    (state : ProverCommitWeightsStorage53.State) (n : Nat) (row : Usize)
    (bound : row.val+n≤1024) (s : Raw) (hs : canonical s) :
    ∃ z : Raw, PV_RunJoin_InactiveFinite48.run n (input q) state (source s) row=ok (source z) ∧
      canonical z ∧ value z=value s+total q n row.val := by
  induction n generalizing row s with
  | zero => exact ⟨s,rfl,hs,by rw [total,add_zero]⟩
  | succ n ih =>
    have hr : row.val<1024 := by omega
    obtain ⟨next,hn,hcn,hdn⟩ := PV_RunJoin_InactiveValueCell48.complete q hq state s hs row hr
    have inc := PV_RunJoin_MergeLoop35.increment row (by omega)
    obtain ⟨z,hz,hcz,hdz⟩ := ih (Usize.wrapping_add row 1#usize) (by rw [inc];omega) next hcn
    refine ⟨z,?_,hcz,?_⟩
    · simp only [PV_RunJoin_InactiveFinite48.run,hn,bind_tc_ok,hz]
    · rw [hdz,hdn,inc,total]
      ring
#print axioms complete
end R1Z.PV_RunJoin_InactiveValue48
