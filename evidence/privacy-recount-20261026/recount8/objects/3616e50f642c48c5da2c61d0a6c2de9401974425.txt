import R1Z.PV_RDB2C_PV_B2_F_RawOriginal
import R1Z.PV_RDB2C_PV_B2_D_RowRange
import R1Z.PV_RDB2C_PV_B2_C_ErrorRepair
set_option autoImplicit false
namespace PV_B2_F_RawGuard
open Aeneas Aeneas.Std Result PV_B2_251c1
/-- Includes arbitrary Usize inputs: an invalid D read fails before inactive;
the two symbolic permutations always return a row below1024. -/
theorem row_bounded (v : transport.Variant) (j r : Usize)
    (hr : host_weights.host_row v j = ok r) : r.val < 1024 := by
  cases v with
  | S1 =>
    rw [PV_B2_D_RowSource.S1] at hr
    cases Result.ok.inj hr
    exact PV_B2_D_RowRange.perm_bound j
  | S2 =>
    rw [PV_B2_D_RowSource.S2] at hr
    cases Result.ok.inj hr
    exact PV_B2_D_RowRange.perm_bound j
  | D =>
    by_cases hj : j.val < (1024#usize).val
    · obtain ⟨a,ha,hb⟩ := PV_B2_D_RowRange.D j hj
      have he : a=r := Result.ok.inj (ha.symm.trans hr)
      exact he ▸ hb
    · have he := PV_B2_C_ErrorRepair.index_failure host_weights.HOST_COEFFICIENT_TO_ROW j
        (Nat.le_of_not_gt hj)
      unfold host_weights.host_row at hr
      rw [he,bind_tc_fail] at hr
      cases hr

/-- Frozen inactive's checked guard and unwrap; the panic branch is explicit. -/
def inactive (w : host_weights.Weights) (j : Usize) : Result aspis_core.field.QM31 := do
  let r ← host_weights.host_row w.variant j
  if r.val < 1024 then
    let row ← r / 16#usize
    let mask ← Array.index_usize aspis_core.r0.opening.COPY_ACTIVE_ROW_MASKS row
    let bit ← r % 16#usize
    if (U16.wrapping_shr mask (UScalar.cast .U32 bit) &&& 1#u16)=0#u16
    then ok aspis_core.field.QM31.ONE else ok aspis_core.field.QM31.ZERO
  else fail .panic

theorem inactive_source (w : host_weights.Weights) (j : Usize) :
    PV_B2_F_RawOriginal.inactive w j = inactive w j := by
  cases hr : host_weights.host_row w.variant j with
  | fail e => simp only [PV_B2_F_RawOriginal.inactive,inactive,hr,bind_tc_fail]
  | div => simp only [PV_B2_F_RawOriginal.inactive,inactive,hr,bind_tc_div]
  | ok r =>
    have hb := row_bounded w.variant j r hr
    simp only [PV_B2_F_RawOriginal.inactive,inactive,hr,bind_tc_ok,if_pos hb]

def original (w : host_weights.Weights) (kind j : Usize) : Result aspis_core.field.QM31 :=
  if kind=0#usize then inactive w j else PV_B2_F_RawOriginal.original w kind j

theorem source (w : host_weights.Weights) (kind j : Usize) :
    host_weights.raw_value w kind j = original w kind j := by
  rw [PV_B2_F_RawOriginal.source]
  unfold original
  by_cases hk : kind=0#usize
  · rw [if_pos hk]
    simp only [PV_B2_F_RawOriginal.original,hk,if_true,inactive_source]
  · rw [if_neg hk]
#print axioms row_bounded
#print axioms inactive_source
#print axioms source
end PV_B2_F_RawGuard
