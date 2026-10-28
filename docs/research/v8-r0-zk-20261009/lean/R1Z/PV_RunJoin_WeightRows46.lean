import R1Z.PV_RunJoin_WeightRaw446
set_option autoImplicit false
noncomputable section
namespace R1Z.PV_RunJoin_WeightRows46
open Aeneas Aeneas.Std Result PV_RunJoin_WeightCarrier46
open PV_RunJoin_WeightMap46 (mapResult)
open PV_RunJoin_WeightInstalled46

theorem raw (w : W) (hs : w.variant=.S2) (kind j : Usize) (hk : kind.val<7) :
    AspisR1ProducerRelease47.weights53.raw (state w) kind j=
      mapResult toQ (PV_B2_251c1.host_weights.raw_value w kind j) := by
  by_cases h0 : kind=0#usize
  · subst kind
    rw [ProverCommitWeightsStorage53.raw_zero]
    exact PV_RunJoin_WeightInactive46.complete w hs j
  by_cases h1 : kind=1#usize
  · subst kind;exact PV_RunJoin_WeightRaw146.complete w hs j
  by_cases h2 : kind=2#usize
  · subst kind;exact PV_RunJoin_WeightRaw246.complete w hs j
  by_cases h3 : kind=3#usize
  · subst kind;exact PV_RunJoin_WeightRaw346.complete w hs j
  by_cases h4 : kind=4#usize
  · subst kind;exact PV_RunJoin_WeightRaw446.complete w j
  by_cases h5 : kind=5#usize
  · subst kind;exact PV_RunJoin_WeightRaw546.complete w hs j
  have h6 : kind=6#usize := by scalar_tac
  subst kind
  exact PV_RunJoin_WeightRaw646.complete w hs j

theorem complete (base : ProverRwFull.ExternalTypes) (heap : Heap) (box : Box)
    (ops : @ProverRwFull.ExternalFuns (types base)) (w : W) (hs : w.variant=.S2)
    (kind j : Usize) (hk : kind.val<7) :
    @ProverRwFull.ExternalFuns.op253 (types base) (selected base heap box ops) w kind j=
      mapResult PV_RunJoin_WeightRawInstalled46.nativeQ
        (AspisR1ProducerRelease47.weights53.raw (state w) kind j) :=
  PV_RunJoin_WeightRawInstalled46.transport base heap box ops w kind j (raw w hs kind j hk)
#print axioms raw
#print axioms complete
end R1Z.PV_RunJoin_WeightRows46
