import NCM_Levels

set_option autoImplicit false
namespace AspisR1.NCM_LevelsDomain
open Aeneas Aeneas.Std Result MultiproofConeRef
open MultiproofConeNodeDomain MultiproofConeNodeIteration MultiproofConeLevelIteration

/-- Final-control bounds are outputs of the same height execution. -/
theorem preserved {X : Type} (D : aspis_core.digest.Digest32 X) (hash : X)
    (hashTotal : HashTotal D hash) (physical : Slice U8) (height : Nat)
    (s after : reference.Scratch) (domain : Domain physical s)
    (returned : iterate (fun state => reference.level_rows D hash state physical 0#usize 0#usize) height s = ok (.Done after)) :
    Domain physical after := by
  induction height generalizing s with
  | zero => cases returned;exact domain
  | succ height ih =>
    obtain ⟨out,step⟩ := NCM_Level.total D hash hashTotal s physical domain
    simp only [iterate,step,bind_tc_ok] at returned
    cases out with
    | Stop stopped => cases returned
    | Done next => exact ih next (level_preserve D hash hashTotal physical s next domain step) returned

#print axioms preserved
end AspisR1.NCM_LevelsDomain
