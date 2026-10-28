import R1Z.PV_RunJoin_WeightProduct46
set_option autoImplicit false
namespace R1Z.PV_RunJoin_WeightTensor46
open Aeneas Aeneas.Std Result PV_RunJoin_WeightCarrier46
open PV_B2_F_ConstructorCarrier (amap)
open PV_RunJoin_WeightMap46 (mapResult)
attribute [local irreducible] PV_B2_251c1.aspis_core.field.QM31.mul

-- Five symbolic accesses, with arithmetic callees opaque.
theorem source (rows : Array (Array Q 4#usize) 5#usize) (j : Usize) :
    PV_B2_251c1.host_weights.tensor_raw rows j=
      PV_RunJoin_WeightProduct46.product rows j 5 0#usize
        PV_B2_251c1.aspis_core.field.QM31.ONE := by
  unfold PV_B2_251c1.host_weights.tensor_raw
  simp only [PV_RunJoin_WeightProduct46.product,lift,bind_tc_ok,bind_assoc,bind_pure]

theorem complete (rows : Array (Array Q 4#usize) 5#usize) (j : Usize) :
    AspisR1ProducerRelease47.stored.product (amap (amap toQ) rows) j 0#usize 5#u8
      AspisR1ProducerRelease47.field.QM31.ONE=
      mapResult toQ (PV_B2_251c1.host_weights.tensor_raw rows j) := by
  rw [source,PV_RunJoin_WeightQuartic46.one]
  exact PV_RunJoin_WeightProduct46.complete rows j 5 0#usize 5#u8 rfl _
#print axioms source
#print axioms complete
end R1Z.PV_RunJoin_WeightTensor46
