import R1Z.PV_RunJoin_WeightCircleLoop47
import R1Z.PV_RunJoin_WeightCircleOverwrite47
import R1Z.PV_RunJoin_WeightPointRows47
set_option autoImplicit false
namespace R1Z.PV_RunJoin_WeightCircleRows47
open Aeneas Aeneas.Std Result
open PV_B2_F_ConstructorCarrier (K amap)
open PV_B2_C_ConstructorRows (Factors)
open PV_RunJoin_WeightFactorWrite47 (Matrix)
open PV_RunJoin_WeightKernel46 (toQ)
open PV_RunJoin_WeightMap46 (mapResult map_bind)

def fill (m : Matrix) (x y : K) : Result Matrix := do
  let row ← PV_RunJoin_WeightCircleFactor46.run x y
  let m1 ← Array.update m 0#usize row
  let next ← PV_RunJoin_WeightDoubleFactor46.run x
  PV_RunJoin_WeightCircleRows46.remaining 4 m1 1#usize next

def run (x y : K) : Result Matrix := fill PV_RunJoin_WeightPointRows47.seed x y

theorem independent (m m1 : Matrix) (x y : K) : fill m x y=fill m1 x y := by
  unfold fill
  apply (Aeneas.Std.bind_eq_iff _ _ _).mpr
  intro row _
  simp only [PV_RunJoin_WeightArrayUpdate47.complete m 0#usize (by decide) row,
    PV_RunJoin_WeightArrayUpdate47.complete m1 0#usize (by decide) row,bind_tc_ok]
  apply (Aeneas.Std.bind_eq_iff _ _ _).mpr
  intro next _
  apply PV_RunJoin_WeightCircleOverwrite47.remaining 4 _ _ 1#usize next (by decide)
  have hf : PV_RunJoin_WeightMatrixFrame47.Frame m m1 (0#usize).val (4+1) := by
    intro i hi h
    have hz : (0#usize).val=0 := by scalar_tac
    rw [hz] at h
    omega
  exact PV_RunJoin_WeightMatrixFrame47.step m m1 0#usize 4 row (by decide) hf
#print axioms independent

theorem source (fs : Factors) (slot : Usize) (x y : K) (hs : slot.val<5) :
    PV_RunJoin_WeightCircleSource47.run fs slot x y=(do
      let m ← run x y;ok (Aeneas.Std.Array.set fs slot m)) := by
  obtain ⟨m,hm,_⟩ := WP.spec_imp_exists (Array.index_usize_spec fs slot (by
    change slot.val<fs.val.length
    rw [fs.property]
    exact hs))
  have hfill : PV_RunJoin_WeightCircleSource47.run fs slot x y=(do
      let m1 ← fill m x y;ok (Aeneas.Std.Array.set fs slot m1)) := by
    unfold PV_RunJoin_WeightCircleSource47.run fill
    simp only [PV_RunJoin_WeightFactorWrite47.equation,hm,bind_tc_ok,bind_assoc]
    apply (Aeneas.Std.bind_eq_iff _ _ _).mpr
    intro row _
    apply (Aeneas.Std.bind_eq_iff _ _ _).mpr
    intro m1 _
    apply (Aeneas.Std.bind_eq_iff _ _ _).mpr
    intro next _
    rw [PV_RunJoin_WeightCircleLoop47.complete 4 _ slot 1#usize next m1
      (PV_RunJoin_WeightFactorWrite47.read_set fs slot m1 hs) hs]
    simp only [PV_RunJoin_WeightFactorWrite47.overwrite]
  rw [hfill,independent m PV_RunJoin_WeightPointRows47.seed]
  rfl
#print axioms source

theorem fill_model (m : Matrix) (x y : K) :
    (do let row ← AspisR1ProducerRelease47.factors.circle (toQ x) (toQ y)
        let m1 ← Array.update (amap (amap toQ) m) 0#usize row
        let next ← AspisR1ProducerRelease47.factors.double (toQ x)
        AspisR1ProducerRelease47.factors.lines m1 1#usize 4#u8 next)=
      mapResult (amap (amap toQ)) (fill m x y) := by
  unfold fill
  rw [PV_RunJoin_WeightCircleFactor46.complete]
  symm
  apply map_bind (amap toQ) (amap (amap toQ))
  intro row
  rw [PV_RunJoin_WeightUpdate46.complete]
  apply map_bind (amap (amap toQ)) (amap (amap toQ))
  intro m1
  rw [PV_RunJoin_WeightDoubleFactor46.complete]
  apply map_bind toQ (amap (amap toQ))
  intro next
  exact (PV_RunJoin_WeightCircleRows46.complete 4 m1 1#usize 4#u8 next rfl).symm
#print axioms fill_model

theorem model (x y : K) : AspisR1ProducerRelease47.factors.circle_rows (toQ x) (toQ y)=
    mapResult (amap (amap toQ)) (run x y) := by
  have hseed : amap (amap toQ) PV_RunJoin_WeightPointRows47.seed=Array.repeat 5#usize
      (Array.repeat 4#usize AspisR1ProducerRelease47.field.QM31.ZERO) := by
    unfold PV_RunJoin_WeightPointRows47.seed
    rw [PV_RunJoin_WeightArray46.replicate,PV_RunJoin_WeightArray46.replicate,
      ←PV_RunJoin_WeightConstructorZero47.complete]
  have h := fill_model PV_RunJoin_WeightPointRows47.seed x y
  rw [hseed] at h
  exact h
#print axioms model
end R1Z.PV_RunJoin_WeightCircleRows47
