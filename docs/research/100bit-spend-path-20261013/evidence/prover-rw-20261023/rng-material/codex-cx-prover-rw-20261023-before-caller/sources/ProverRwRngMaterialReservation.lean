import R1Z.ProverRwRngMaterialFinish
set_option autoImplicit false
noncomputable section
namespace R1Z.ProverRwRngMaterialReservation
open Aeneas Aeneas.Std Result ProverRwRngMaterialBody
open aspis_prover.state_only_entropy aspis_prover.state_only_hiding
open aspis_core.state_only_hiding ProverRwRngMaterialControl ProverRwRngMaterialFinish
open ProverRwRngMaterialInvariant
variable [TypeLeaves] [LocalLeaves]
abbrev Status := core.result.Result (ReservedStateOnlyAttemptSecrets × StateOnlyMaskMaterial) BuildError
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

#print axioms reservation_invariant
end R1Z.ProverRwRngMaterialReservation
