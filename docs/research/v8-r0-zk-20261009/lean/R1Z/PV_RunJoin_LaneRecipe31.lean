import R1Z.PV_RunJoin_LaneFold31
import R1Z.BuilderRecordsFields
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
  constructor
  · intro h
    unfold recipe at h
    obtain ⟨r,hr,htail⟩ := BuilderRecordsFields.bind_ok_inv h
    cases r with
    | Err e => cases htail
    | Ok d =>
      obtain ⟨out,hout,hret⟩ := BuilderRecordsFields.bind_ok_inv htail
      cases Result.ok.inj hret
      exact ⟨d,hr,hout⟩
  · rintro ⟨d,hd,hroot⟩
    unfold recipe
    rw [hd]
    simp only [bind_tc_ok]
    rw [hroot]
    rfl

#print axioms recipe_success
end R1Z.PV_RunJoin_LaneRecipe31
