import R1Z.BuilderRecordsExtracted

/-! Successful owned-reference mapping preserves the explicit output/change
values and asset. This is a theorem about the extracted reference only;
shipped-records equivalence and the canonical witness map remain separate. -/
set_option autoImplicit false
namespace R1Z.BuilderRecordsFields
open Aeneas Aeneas.Std Result AspisBuilderRecordsReference
open pool_v1.pair_forest_copy_builder

theorem bind_ok_inv {α β : Type} {x : Result α} {f : α → Result β} {t : β}
    (h : (do let a ← x; f a) = ok t) : ∃ a, x = ok a ∧ f a = ok t := by
  cases x with
  | ok a => exact ⟨a, rfl, by simpa using h⟩
  | fail e => simp at h
  | div => simp at h

theorem fixed_fields
    (input : pool_v1.pair_forest_trace.PoolV1PairForestInputNoteWitnessV1)
    (out : U32) (rec : Option pool_v1.payment_relation.PoolV1OutputNoteWitnessV1)
    (chg : pool_v1.payment_relation.PoolV1OutputNoteWitnessV1)
    (snapshot : pool_v1.pair_tree_profile.PoolV1PairLiveSnapshotV1)
    (asset : aspis_core.field.M31)
    (empty : Array (Array aspis_core.field.M31 8#usize) 21#usize)
    (w : RW) (p : RP)
    (h : records_reference.records_reference_with_roots
      input out rec chg snapshot asset empty = ok (w, p)) :
    w.output_value = out ∧ w.change_value = chg.value ∧ p.asset = asset := by
  unfold records_reference.records_reference_with_roots at h
  obtain ⟨⟨pair, bits, sibs⟩, _, h⟩ := bind_ok_inv h
  obtain ⟨⟨rec1, owner, salt⟩, _, h⟩ := bind_ok_inv h
  obtain ⟨⟨snapshot1, frontier, empty1⟩, _, h⟩ := bind_ok_inv h
  obtain ⟨sk, _, h⟩ := bind_ok_inv h
  obtain ⟨salt1, _, h⟩ := bind_ok_inv h
  obtain ⟨first, _, h⟩ := bind_ok_inv h
  obtain ⟨second, _, h⟩ := bind_ok_inv h
  obtain ⟨owner1, _, h⟩ := bind_ok_inv h
  obtain ⟨salt2, _, h⟩ := bind_ok_inv h
  obtain ⟨rfl, rfl⟩ := Prod.mk.inj (Result.ok.inj h)
  exact ⟨rfl, rfl, rfl⟩

#print axioms bind_ok_inv
#print axioms fixed_fields
end R1Z.BuilderRecordsFields
