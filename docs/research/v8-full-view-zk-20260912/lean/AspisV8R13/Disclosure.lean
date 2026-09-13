import AspisV8R13.MovingLeaves

/-! A salt already disclosed cannot be treated as a hidden 256-bit guess.
Freeze the corresponding group or prove the exact payload equality needed. -/
set_option autoImplicit false
namespace AspisV8R13
variable {Index Key Digest : Type*} [DecidableEq Key]

theorem disclosed_group_unchanged
    (H : LeafOracle Index Key Digest) (old new : Index → Key) (i : Index)
    (fixed : old i = new i) : (swapFamilies H old new) i = H i := by
  simp [swapFamilies, fixed]

/-- Preserving the root is not the same as preserving a serialized opening. -/
theorem equal_opening_requires_equal_payload
    {Salt Payload Hash : Type*} (s : Salt) (p q : Payload) (h : Hash)
    (sameOpening : (s,p,h) = (s,q,h)) : p = q := by
  exact congrArg (fun x : Salt × Payload × Hash => x.2.1) sameOpening

#print axioms disclosed_group_unchanged
#print axioms equal_opening_requires_equal_payload
end AspisV8R13
