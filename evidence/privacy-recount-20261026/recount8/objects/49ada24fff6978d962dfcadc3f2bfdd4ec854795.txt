import R1Z.PV_RunJoin_WeightInstalled46
import R1Z.PV_RunJoin_WeightInactive46
import R1Z.PV_RunJoin_WeightRaw146
import R1Z.PV_RunJoin_WeightRaw246
import R1Z.PV_RunJoin_WeightRaw346
import R1Z.PV_RunJoin_WeightRaw546
import R1Z.PV_RunJoin_WeightRaw646
import R1Z.PV_RunJoin_WeightArray46
set_option autoImplicit false
noncomputable section
namespace R1Z.PV_RunJoin_WeightRawInstalled46
open Aeneas Aeneas.Std Result PV_RunJoin_WeightCarrier46
open PV_RunJoin_WeightInstalled46
open PV_RunJoin_WeightMap46 (mapResult)

def nativeQ (q : MQ) : PV_B2_F_ConstructorCarrier.NQ := PV_B2_F_RawNative.toNativeQ (fromQ q)

theorem transport (base : ProverRwFull.ExternalTypes) (heap : Heap) (box : Box)
    (ops : @ProverRwFull.ExternalFuns (types base)) (w : W) (kind j : Usize)
    (hraw : AspisR1ProducerRelease47.weights53.raw (state w) kind j=
      mapResult toQ (PV_B2_251c1.host_weights.raw_value w kind j)) :
    @ProverRwFull.ExternalFuns.op253 (types base) (selected base heap box ops) w kind j=
      mapResult nativeQ (AspisR1ProducerRelease47.weights53.raw (state w) kind j) := by
  rw [PV_RunJoin_WeightInstalled46.raw]
  change mapResult PV_B2_F_RawNative.toNativeQ (PV_B2_F_RawGuard.original w kind j)=_
  rw [← PV_B2_F_RawGuard.source,hraw,PV_RunJoin_WeightArray46.result_comp]
  have hc : (fun q => nativeQ (toQ q))=PV_B2_F_RawNative.toNativeQ := by
    funext q
    exact congrArg PV_B2_F_RawNative.toNativeQ (q_roundtrip q)
  rw [hc]
#print axioms transport

theorem raw0 (base : ProverRwFull.ExternalTypes) (heap : Heap) (box : Box)
    (ops : @ProverRwFull.ExternalFuns (types base)) (w : W) (hs : w.variant=.S2) (j : Usize) :
    @ProverRwFull.ExternalFuns.op253 (types base) (selected base heap box ops) w 0#usize j=
      mapResult nativeQ (AspisR1ProducerRelease47.weights53.raw (state w) 0#usize j) :=
  transport base heap box ops w 0#usize j (by
      rw [ProverCommitWeightsStorage53.raw_zero]
      exact PV_RunJoin_WeightInactive46.complete w hs j)
#print axioms raw0

theorem raw1 (base : ProverRwFull.ExternalTypes) (heap : Heap) (box : Box)
    (ops : @ProverRwFull.ExternalFuns (types base)) (w : W) (hs : w.variant=.S2) (j : Usize) :
    @ProverRwFull.ExternalFuns.op253 (types base) (selected base heap box ops) w 1#usize j=
      mapResult nativeQ (AspisR1ProducerRelease47.weights53.raw (state w) 1#usize j) :=
  transport base heap box ops w 1#usize j (PV_RunJoin_WeightRaw146.complete w hs j)
#print axioms raw1

theorem raw2 (base : ProverRwFull.ExternalTypes) (heap : Heap) (box : Box)
    (ops : @ProverRwFull.ExternalFuns (types base)) (w : W) (hs : w.variant=.S2) (j : Usize) :
    @ProverRwFull.ExternalFuns.op253 (types base) (selected base heap box ops) w 2#usize j=
      mapResult nativeQ (AspisR1ProducerRelease47.weights53.raw (state w) 2#usize j) :=
  transport base heap box ops w 2#usize j (PV_RunJoin_WeightRaw246.complete w hs j)
#print axioms raw2

theorem raw3 (base : ProverRwFull.ExternalTypes) (heap : Heap) (box : Box)
    (ops : @ProverRwFull.ExternalFuns (types base)) (w : W) (hs : w.variant=.S2) (j : Usize) :
    @ProverRwFull.ExternalFuns.op253 (types base) (selected base heap box ops) w 3#usize j=
      mapResult nativeQ (AspisR1ProducerRelease47.weights53.raw (state w) 3#usize j) :=
  transport base heap box ops w 3#usize j (PV_RunJoin_WeightRaw346.complete w hs j)
#print axioms raw3

theorem raw5 (base : ProverRwFull.ExternalTypes) (heap : Heap) (box : Box)
    (ops : @ProverRwFull.ExternalFuns (types base)) (w : W) (hs : w.variant=.S2) (j : Usize) :
    @ProverRwFull.ExternalFuns.op253 (types base) (selected base heap box ops) w 5#usize j=
      mapResult nativeQ (AspisR1ProducerRelease47.weights53.raw (state w) 5#usize j) :=
  transport base heap box ops w 5#usize j (PV_RunJoin_WeightRaw546.complete w hs j)
#print axioms raw5

theorem raw6 (base : ProverRwFull.ExternalTypes) (heap : Heap) (box : Box)
    (ops : @ProverRwFull.ExternalFuns (types base)) (w : W) (hs : w.variant=.S2) (j : Usize) :
    @ProverRwFull.ExternalFuns.op253 (types base) (selected base heap box ops) w 6#usize j=
      mapResult nativeQ (AspisR1ProducerRelease47.weights53.raw (state w) 6#usize j) :=
  transport base heap box ops w 6#usize j (PV_RunJoin_WeightRaw646.complete w hs j)
#print axioms raw6
end R1Z.PV_RunJoin_WeightRawInstalled46
