import R1Z.PV_RunJoin_WeightPower46
import R1Z.PV_RunJoin_WeightRawInstalled46
set_option autoImplicit false
namespace R1Z.PV_RunJoin_WeightRaw446
open Aeneas Aeneas.Std Result PV_RunJoin_WeightCarrier46
open PV_B2_F_ConstructorCarrier (amap)
open PV_RunJoin_WeightMap46 (mapResult map_bind)

theorem complete (w : W) (j : Usize) :
    AspisR1ProducerRelease47.weights53.raw (state w) 4#usize j=
      mapResult toQ (PV_B2_251c1.host_weights.raw_value w 4#usize j) := by
  change AspisR1ProducerRelease47.extras.libra (amap toQ w.extra) j=_
  rw [PV_B2_F_RawOriginal.source]
  simp only [PV_B2_F_RawOriginal.original,
    show ¬ (4#usize=0#usize) from by decide,if_false,if_true]
  unfold AspisR1ProducerRelease47.extras.libra PV_B2_F_RawOriginal.extra
  by_cases hj : j<56#usize
  · simp only [hj,if_true]
    obtain ⟨d,hd,_⟩ := ProverCommitInactiveRow49.div_value j 28#usize (by decide)
    obtain ⟨e,he,hv⟩ := ProverCommitInactiveRow49.rem_value j 28#usize (by decide)
    have hb : e.val<28 := by rw [hv];exact Nat.mod_lt _ (by decide)
    have h8 : (UScalar.cast .U8 e).val=e.val := by
      rw [PV_B2_D_SmallScalar.cast_val]
      change e.val%256=e.val
      exact Nat.mod_eq_of_lt (by omega)
    have h64 : (UScalar.cast .U64 e).val=e.val := by
      rw [PV_B2_D_SmallScalar.cast_val]
      change e.val%18446744073709551616=e.val
      exact Nat.mod_eq_of_lt (by omega)
    simp only [hd,he,lift,bind_tc_ok]
    rw [PV_RunJoin_WeightMap46.index]
    symm
    apply map_bind toQ toQ
    intro q
    exact (PV_RunJoin_WeightPower46.complete q _ _ (h64.trans h8.symm)).symm
  · simp only [hj,if_false,mapResult,PV_B2_E_OrdinaryOriginal.mapResult,
      PV_RunJoin_WeightQuartic46.zero]
#print axioms complete
end R1Z.PV_RunJoin_WeightRaw446
