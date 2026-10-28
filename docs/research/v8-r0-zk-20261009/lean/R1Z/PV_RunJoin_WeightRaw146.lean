import R1Z.PV_RunJoin_WeightRawTensor46
set_option autoImplicit false
namespace R1Z.PV_RunJoin_WeightRaw146
open Aeneas Aeneas.Std Result PV_RunJoin_WeightCarrier46
open PV_B2_F_ConstructorCarrier (amap)
open PV_RunJoin_WeightMap46 (mapResult map_bind)

theorem complete (w : W) (hs : w.variant=.S2) (j : Usize) :
    AspisR1ProducerRelease47.weights53.raw (state w) 1#usize j=
      mapResult toQ (PV_B2_251c1.host_weights.raw_value w 1#usize j) := by
  rw [PV_RunJoin_WeightRawTensor46.source w hs 1#usize j (by decide) (by decide)]
  change (do
    let idx ← if 1#usize<4#usize then ok (Usize.wrapping_sub 1#usize 1#usize)
      else ok (Usize.wrapping_sub 1#usize 2#usize)
    let rows ← Array.index_usize (amap (amap (amap toQ)) w.factors) idx
    AspisR1ProducerRelease47.stored.product rows j 0#usize 5#u8
      AspisR1ProducerRelease47.field.QM31.ONE)=_
  rw [PV_RunJoin_WeightResult46.shared_bind]
  apply (Aeneas.Std.bind_eq_iff _ _ _).mpr
  intro idx _
  dsimp only
  have hi := PV_RunJoin_WeightMap46.index (amap (amap toQ)) w.factors idx
  rw [hi]
  symm
  apply map_bind (amap (amap toQ)) toQ
  intro rows
  exact (PV_RunJoin_WeightTensor46.complete rows j).symm
#print axioms complete
end R1Z.PV_RunJoin_WeightRaw146
