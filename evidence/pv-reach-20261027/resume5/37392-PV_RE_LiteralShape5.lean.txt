import R1Z.ProverRwFullFuns
set_option autoImplicit false
noncomputable section
namespace R1Z.PV_RE_LiteralShape5
open Aeneas Aeneas.Std Result
/-- Exact exceptional matcher in validate_pool_v1_context. Its branches are
pure successes: inspect three symbolic branches, never reduce a recurrence. -/
def legacy (x : U64) : Result (U64 × Bool) :=
  match x with
  | 2974012453224067339#uscalar => .ok (2974012453224067339#u64, true)
  | 1731042625218380614#uscalar => .ok (1731042625218380614#u64, true)
  | _ => .ok (x, false)

theorem legacy_success (x : U64) : ∃ out, legacy x = .ok out := by
  unfold legacy
  split <;> exact ⟨_, rfl⟩

/-- This entire scalar matcher has no outer failure or divergence on any input. -/
theorem legacy_not_fail (x : U64) (e : Error) : legacy x ≠ .fail e := by
  obtain ⟨out, h⟩ := legacy_success x
  rw [h]
  intro bad
  cases bad

theorem legacy_not_div (x : U64) : legacy x ≠ .div := by
  obtain ⟨out, h⟩ := legacy_success x
  rw [h]
  intro bad
  cases bad

#print axioms legacy_success
#print axioms legacy_not_fail
#print axioms legacy_not_div
end R1Z.PV_RE_LiteralShape5
