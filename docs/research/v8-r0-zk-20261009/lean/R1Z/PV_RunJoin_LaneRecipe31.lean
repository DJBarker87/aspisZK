import R1Z.PV_RunJoin_LaneFold31
set_option autoImplicit false
noncomputable section
namespace R1Z.PV_RunJoin_LaneRecipe31
open Aeneas Aeneas.Std Result
open PV_RunJoin_LaneFold31

/-- Leaf validation precedes all parent calls; the Rust error is preserved. -/
def recipe {E F : Type} (leaf : Result (core.result.Result Digest E))
    (mapError : E → F) (parent : Digest → Digest → Result Digest)
    (sibling : Nat → Digest) (reverse : Nat → Bool) (levels : List Nat) :
    Result (core.result.Result Digest F) := do
  match ← leaf with
  | .Err e => ok (.Err (mapError e))
  | .Ok d =>
      let root ← fold parent sibling reverse levels d
      ok (.Ok root)

theorem recipe_success {E F : Type} (leaf : Result (core.result.Result Digest E))
    (mapError : E → F) (parent : Digest → Digest → Result Digest)
    (sibling : Nat → Digest) (reverse : Nat → Bool) (levels : List Nat) (root : Digest) :
    recipe leaf mapError parent sibling reverse levels = ok (.Ok root) ↔
      ∃ d, leaf = ok (.Ok d) ∧ fold parent sibling reverse levels d = ok root := by
  cases hleaf : leaf with
  | fail e => simp only [recipe,hleaf,bind_tc_fail]; constructor <;> intro h <;> cases h
  | div => simp only [recipe,hleaf,bind_tc_div]; constructor <;> intro h <;> cases h
  | ok r =>
    cases r with
    | Err e => simp only [recipe,hleaf,bind_tc_ok]; constructor <;> intro h <;> cases h
    | Ok d =>
      simp only [recipe,hleaf,bind_tc_ok]
      cases hfold : fold parent sibling reverse levels d <;>
        simp only [bind_tc_ok,bind_tc_fail,bind_tc_div]
      all_goals constructor
      all_goals first
        | (intro h; cases h)
        | (intro h; exact ⟨d,rfl,by cases h; rfl⟩)
        | (rintro ⟨d',he,h⟩; cases he; cases h; rfl)
#print axioms recipe_success
end R1Z.PV_RunJoin_LaneRecipe31
