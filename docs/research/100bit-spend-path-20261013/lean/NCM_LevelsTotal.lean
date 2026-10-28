import NCM_Level

set_option autoImplicit false
noncomputable section
namespace AspisR1.NCM_LevelsTotal
open Aeneas Aeneas.Std Result MultiproofConeRef
open MultiproofConeNodeDomain MultiproofConeNodeIteration MultiproofConeLevelIteration

/-- Domain is inherited after every actual successful level; short rejection
stops immediately. No accepted-height premise is added. -/
theorem total {X : Type} (D : aspis_core.digest.Digest32 X) (hash : X)
    (hashTotal : HashTotal D hash) (physical : Slice U8) (height : Nat)
    (s : reference.Scratch) (domain : Domain physical s) :
    ∃ out, iterate (fun state => reference.level_rows D hash state physical 0#usize 0#usize) height s = ok out := by
  induction height generalizing s with
  | zero => exact ⟨.Done s,rfl⟩
  | succ height ih =>
    obtain ⟨out,returned⟩ := NCM_Level.total D hash hashTotal s physical domain
    simp only [iterate,returned,bind_tc_ok]
    cases out with
    | Stop stopped => exact ⟨.Stop stopped,rfl⟩
    | Done after => exact ih after (level_preserve D hash hashTotal physical s after domain returned)

#print axioms total
end AspisR1.NCM_LevelsTotal
end
