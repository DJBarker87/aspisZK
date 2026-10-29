import R1Z.PV_RunJoin_WeightPointRowStage047
import R1Z.PV_RunJoin_WeightPointRowOverwrite47
import R1Z.PV_RunJoin_WeightConstructorZero47
set_option autoImplicit false
namespace R1Z.PV_RunJoin_WeightPointRows47
open Aeneas Aeneas.Std Result
open PV_B2_F_ConstructorCarrier (K amap)
open PV_RunJoin_WeightKernel46 (toQ)
open PV_RunJoin_WeightMap46 (mapResult)
open PV_RunJoin_WeightFactorWrite47 (Matrix)
open PV_RunJoin_WeightPointRowStages47 (Point stage0)
open PV_B2_C_ConstructorRows (Factors)

def seed : Matrix := Array.repeat 5#usize (Array.repeat 4#usize PV_B2_C_WeightsNative.aspis_core.field.QM31.ZERO)
def run (p : Point) : Result Matrix := PV_RunJoin_WeightPointRows46.remaining p 5 seed 0#usize

theorem source (p : Point) (fs : Factors) (slot : Usize) (hs : slot.val<5) :
    stage0 p fs slot=(do let m ← run p;ok (Aeneas.Std.Array.set fs slot m)) := by
  obtain ⟨m,hm,_⟩ := WP.spec_imp_exists (Array.index_usize_spec fs slot (by
    change slot.val<fs.val.length
    rw [fs.property]
    exact hs))
  rw [PV_RunJoin_WeightPointRowStage047.complete p fs slot m hm hs,
    PV_RunJoin_WeightPointRowOverwrite47.complete p m seed]
  rfl
#print axioms source

theorem model (p : Point) : AspisR1ProducerRelease47.point_rows.all (amap toQ p)=
    mapResult (amap (amap toQ)) (run p) := by
  unfold AspisR1ProducerRelease47.point_rows.all run
  rw [PV_RunJoin_WeightConstructorZero47.complete]
  rw [←PV_RunJoin_WeightArray46.replicate,←PV_RunJoin_WeightArray46.replicate]
  exact PV_RunJoin_WeightPointRows46.complete p 5 seed 0#usize 5#u8 rfl
#print axioms model
end R1Z.PV_RunJoin_WeightPointRows47
