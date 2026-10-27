import CPH_FixtureKeys
set_option autoImplicit false
noncomputable section
namespace AspisR1.CPH_FixtureEntry
open Aeneas Aeneas.Std Result S2Trust S2W_D189Entry S2W_D189Wrappers
open CPH_FixtureData

theorem valid (e : Entry) (separate : ∀ a, (e.handles a).1 ≠ (e.handles a).2) :
    Valid e.heap := by
  refine ⟨List.Pairwise.nil,?_,?_,?_⟩
  · intro c
    simp [Entry.heap,count,minCounter,maxCounter]
  · intro g member
    cases member
  · intro a live
    exact ⟨separate a,rfl⟩

theorem native_keys (i j : Nat) (hi : i < 256) (hj : j < 256)
    (same : (key i).val.map S2W_ReturnedCheckpoint.nativeByte =
      (key j).val.map S2W_ReturnedCheckpoint.nativeByte) : i = j := by
  have head := congrArg (fun xs : List UInt8 => xs[0]?) same
  change some (S2W_ReturnedCheckpoint.nativeByte (byte i)) =
    some (S2W_ReturnedCheckpoint.nativeByte (byte j)) at head
  have nums := congrArg UInt8.toNat (Option.some.inj head)
  change (UInt8.ofNat (byte i).val).toNat = (UInt8.ofNat (byte j).val).toNat at nums
  rw [UInt8.toNat_ofNat_of_lt' (byte i).bv.isLt,
    UInt8.toNat_ofNat_of_lt' (byte j).bv.isLt,
    CPH_FixtureKeys.byte_value i hi,CPH_FixtureKeys.byte_value j hj] at nums
  exact nums

/-- Generic constructor only for fixture entry consistency, not extraction. -/
theorem admitted (e : Entry) (n : Nat)
    (separate : ∀ a, (e.handles a).1 ≠ (e.handles a).2)
    (bounded : ∀ a, a < n → (e.handles a).1 < 256)
    (keys : ∀ c, (e.records c).owned.key = key c) :
    S2W_D189Consolidation.RuntimeEntrypointAdmission (model (Nat → Record)) e e.heap n where
  entry := {
    valid := valid e separate
    freshGuards := rfl
    noExternalBorrows := fun _ => rfl
    liveAccount := fun _ _ => rfl
    counterZero := fun _ _ => rfl
    sharedCellsOnlyEqualKeys := by
      intro a b ha hb same
      change ((e.records (e.handles a).1).owned.key).val.map _ =
        ((e.records (e.handles b).1).owned.key).val.map _
      rw [same]
    duplicateKeysShareCell := by
      intro a b ha hb same
      change ((e.records (e.handles a).1).owned.key).val.map _ =
        ((e.records (e.handles b).1).owned.key).val.map _ at same
      rw [keys,keys] at same
      exact native_keys _ _ (bounded a ha) (bounded b hb) same }
  related := rfl

#print axioms valid
#print axioms native_keys
#print axioms admitted
end AspisR1.CPH_FixtureEntry
end
