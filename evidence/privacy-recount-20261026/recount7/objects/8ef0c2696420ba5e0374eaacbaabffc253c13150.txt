import R1Z.PV_Src_ForestTrace

/-! Identify the merged column returned by the actual CopyRecords.banks
wrapper. This retains its success guard; Parts totality is proved separately.
No record mapper, forest-admission or semantic-validity fact is assumed. -/
set_option autoImplicit false
namespace R1Z.PV_Src_ForestBanks
open Aeneas Aeneas.Std Result
open BuilderForestAdmissionPort.pool_v1.pair_forest_copy_builder
open BuilderRecordsFields

theorem merged_run (records : CopyRecords) (banks : CopyBanks)
    (h : CopyRecords.banks records = ok (some banks)) :
    PV_Src_ForestTrace.run records.w records.p = ok banks.merged := by
  unfold CopyRecords.banks at h
  obtain ⟨⟨good,stable,late,merged⟩,hm,h⟩ := bind_ok_inv h
  cases good with
  | false => simp at h
  | true =>
    simp only [if_true] at h
    obtain ⟨cs,hs,h⟩ := bind_ok_inv h
    obtain ⟨cl,hl,h⟩ := bind_ok_inv h
    obtain ⟨cm,hc,h⟩ := bind_ok_inv h
    have he : cm = banks.merged := by
      have h' := Option.some.inj (Result.ok.inj h)
      exact congrArg CopyBanks.merged h'
    rw [PV_Src_ForestTrace.run,hm]
    simp only [bind_tc_ok]
    exact hc.trans (congrArg Result.ok he)

theorem merged_trace {K : Type} [Field K] [Fintype K] [DecidableEq K]
    [Algebra (ZMod AspisCircleGroupOrder.P) K] [CharP K 2147483647]
    (records : CopyRecords) (banks : CopyBanks)
    (h : CopyRecords.banks records = ok (some banks)) :
    (fun (c : Fin 29) (r : Fin 1024) => R0Z.WriterRefine.liftU (K := K)
      (PV_Src_Forest_Columns.read banks.merged c r)) =
      PV_Src_ForestTrace.trace records.w records.p := by
  funext c r
  change _ = R0Z.WriterRefine.liftU
    (PV_Src_Forest_Columns.read (R0Z.WriterRefine.okOr
      (PV_Src_ForestTrace.run records.w records.p) _) c r)
  rw [merged_run records banks h,R0Z.WriterRefine.okOr_ok]

#print axioms merged_run
#print axioms merged_trace
end R1Z.PV_Src_ForestBanks
