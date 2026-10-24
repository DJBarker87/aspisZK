import R1Z.ProverRwRngNativeBuildPaths
set_option autoImplicit false
noncomputable section
namespace R1Z.ProverRwRngNativeReservationInvariant
open Aeneas Aeneas.Std Result ProverRwRngNativeBody
open aspis_prover.state_only_entropy aspis_prover.state_only_hiding
open aspis_core.state_only_hiding ProverRwRngNativeReserve ProverRwRngNativeBuildControl
open ProverRwRngNativeBuildPaths
variable [TypeLeaves] [LocalLeaves]
abbrev Status := core.result.Result (ReservedStateOnlyAttemptSecrets × StateOnlyMaskMaterial) BuildError
abbrev clearEntropy (a : Secrets) :=
  zeroize.Zeroizing.Insts.ZeroizeZeroize.zeroize
    (Array.Insts.ZeroizeZeroize 32#usize (zeroize.Zeroize.Blanket U8.Insts.ZeroizeDefaultIsZeroes))
    a.field_mask_entropy

def Returns {T : Type} (p : T → Prop) (r : Result T) : Prop :=
  ∀ out, r = .ok out → p out

omit [TypeLeaves] [LocalLeaves] in
theorem returns_bind {A B : Type} (p : B → Prop) (r : Result A) (f : A → Result B)
    (next : ∀ a, r = .ok a → Returns p (f a)) : Returns p (r >>= f) := by
  cases r with
  | fail e => intro out h; cases h
  | div => intro out h; cases h
  | ok a => exact next a rfl

def AfterReserve {S : Type} (a : Secrets) (after : S) (out : Status × S) : Prop :=
  out.2 = after ∧
  (∀ material, out.1 = .Ok material → ∃ cleared, clearEntropy a = .ok cleared)

/-- All admitted outcomes after a successful reservation retain its advanced
store. Every successful material result traverses the actual explicit clear
call. This asserts admission of that leaf, not physical memory zeroization. -/
theorem reservation_invariant {S : Type} (store : Store S) (a : Secrets)
    (hash : Hash) (binding : Array U8 32#usize) (c : Context) (s after : S)
    (layout : LayoutOk a c)
    (reserved : store.reserve s c.statement_digest c.mask_nonce = .ok (true,after)) :
    Returns (AfterReserve a after) (reserveBuild store a hash binding c s) := by
  rcases layout with ⟨nonce,mask,factor⟩
  have compare : core.array.equality.PartialEqArray.ne core.cmp.PartialEqU8
      c.mask_nonce a.mask_nonce = .ok false := by rw [nonce,array_ne_self]
  unfold reserveBuild StateOnlyAttemptSecrets.reserve_and_build_pool_v1_pair_forest_mask_material_v1
  simp only [compare,bind_tc_ok,Bool.false_eq_true,if_false]
  simp [mask,factor,reserved]
  apply returns_bind
  intro entropy hderef
  apply returns_bind
  rintro ⟨status,ack⟩ hbuild
  simp only [Aeneas.Std.uncurry]
  cases status with
  | Err e =>
    change Returns (AfterReserve a after) (.ok (.Err e,after))
    intro out h
    cases h
    exact ⟨rfl,by intro material impossible; cases impossible⟩
  | Ok material =>
    simp only [core.result.Result.Insts.CoreOpsTry.branch,bind_tc_ok]
    split
    · simp only [lift,bind_tc_ok]
      apply returns_bind
      intro encoded hencode
      apply returns_bind
      intro entropySlice hasref
      apply returns_bind
      intro seed hhash
      apply returns_bind
      intro sourceSeed hnew
      apply returns_bind
      intro erased hclear
      intro out h
      cases h
      exact ⟨rfl,by intro output same; exact ⟨erased,hclear⟩⟩
    · intro out h
      cases h
      exact ⟨rfl,by intro material impossible; cases impossible⟩

#print axioms returns_bind
#print axioms reservation_invariant
end R1Z.ProverRwRngNativeReservationInvariant
