import R1Z.PV_RunJoin_CodecOuter30
set_option autoImplicit false
noncomputable section
namespace R1Z.PV_RunJoin_CodecOuterErrors30
open Aeneas Aeneas.Std Result PV_RunJoin_Outer30 PV_RunJoin_CodecOuter30

theorem snapshot_error {C E : Type} (bytes : Slice U8)
    (f : pool_v1.pair_tree_profile.PoolV1PairLiveSnapshotV1 → Result (Aeneas.Std.core.result.Result C E))
    (e : SnapshotError) : run bytes f = ok (.Err (.snapshot e)) ↔
      PV_RunJoin_CodecError29.Path bytes e := by
  constructor
  · intro h
    unfold run at h
    pv_peel h with decoded hd
    cases decoded with
    | Err d =>
      cases Result.ok.inj h
      exact (PV_RunJoin_CodecError29.iff_path bytes e).mp hd
    | Ok s =>
      pv_peel h with compiled hc
      cases compiled <;> cases h
  · intro h
    have hd := (PV_RunJoin_CodecError29.iff_path bytes e).mpr h
    unfold run decode
    rw [hd]
    rfl
#print axioms snapshot_error

theorem trace_error {C E : Type} (bytes : Slice U8)
    (f : pool_v1.pair_tree_profile.PoolV1PairLiveSnapshotV1 → Result (Aeneas.Std.core.result.Result C E))
    (e : E) : run bytes f = ok (.Err (.trace e)) ↔
      PV_RunJoin_CodecComposition30.Path bytes (fun s => f (snapshot s) = ok (.Err e)) := by
  constructor
  · intro h
    unfold run at h
    pv_peel h with decoded hd
    cases decoded with
    | Err d => cases h
    | Ok s =>
      pv_peel h with compiled hc
      cases compiled with
      | Ok c => cases h
      | Err d =>
        cases Result.ok.inj h
        exact (PV_RunJoin_CodecComposition30.source_iff bytes _).mp ⟨s,hd,hc⟩
  · intro h
    obtain ⟨s,hd,hc⟩ := (PV_RunJoin_CodecComposition30.source_iff bytes _).mpr h
    unfold run decode
    rw [hd]
    simp only [bind_tc_ok]
    rw [hc]
    rfl
#print axioms trace_error

theorem post_congr (bytes : Slice U8) (p q : Snapshot → Prop) (h : ∀ s, p s ↔ q s) :
    PV_RunJoin_CodecComposition30.Path bytes p ↔ PV_RunJoin_CodecComposition30.Path bytes q := by
  rw [← PV_RunJoin_CodecComposition30.source_iff,← PV_RunJoin_CodecComposition30.source_iff]
  constructor
  · rintro ⟨s,hd,hp⟩
    exact ⟨s,hd,(h s).mp hp⟩
  · rintro ⟨s,hd,hq⟩
    exact ⟨s,hd,(h s).mpr hq⟩
#print axioms post_congr
end R1Z.PV_RunJoin_CodecOuterErrors30
