import R1Z.PV_CB3_WeightsPickSource
import R1Z.PV_CB3_StagedTotal
set_option autoImplicit false
namespace R1Z.PV_CB3_WeightsPickSpec
open Aeneas Aeneas.Std Result ProverRwFull

theorem source (xs : Array aspis_core.field.QM31 4#usize) (i : Usize) (hi : i.val < 4) :
    PV_CB3_WeightsPickSource.resume6_tensor_reference.pick4 xs i = Array.index_usize xs i := by
  unfold PV_CB3_WeightsPickSource.resume6_tensor_reference.pick4
  rw [PV_CB3_StagedTotal.read_eq xs 0#usize (by decide),
    PV_CB3_StagedTotal.read_eq xs 1#usize (by decide),
    PV_CB3_StagedTotal.read_eq xs 2#usize (by decide),
    PV_CB3_StagedTotal.read_eq xs 3#usize (by decide),
    PV_CB3_StagedTotal.read_eq xs i hi]
  simp only [bind_tc_ok]
  interval_cases h : i.val <;> simp [h]

theorem failure (xs : Array aspis_core.field.QM31 4#usize) (i : Usize) (hi : 4 ≤ i.val) :
    PV_CB3_WeightsPickSource.resume6_tensor_reference.pick4 xs i = fail .panic := by
  unfold PV_CB3_WeightsPickSource.resume6_tensor_reference.pick4
  rw [PV_CB3_StagedTotal.read_eq xs 0#usize (by decide),
    PV_CB3_StagedTotal.read_eq xs 1#usize (by decide),
    PV_CB3_StagedTotal.read_eq xs 2#usize (by decide),
    PV_CB3_StagedTotal.read_eq xs 3#usize (by decide)]
  simp only [bind_tc_ok]
  split <;> rename_i h <;> first | omega | rfl

/-- All four digit inputs succeed, with arbitrary raw field representatives. -/
theorem total (xs : Array aspis_core.field.QM31 4#usize) (i : Usize) (hi : i.val < 4) :
    ∃ q, PV_CB3_WeightsPickSource.resume6_tensor_reference.pick4 xs i = ok q := by
  rw [source xs i hi,PV_CB3_StagedTotal.read_eq xs i hi]
  exact ⟨_,rfl⟩
#print axioms source
#print axioms failure
#print axioms total
end R1Z.PV_CB3_WeightsPickSpec
