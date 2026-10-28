import R1Z.PV_RunJoin_WeightPointFactor46
import R1Z.PV_RunJoin_WeightUpdate46
import R1Z.PV_RunJoin_WeightResult46
import AspisR1ProducerRelease47.PointRows49
set_option autoImplicit false
namespace R1Z.PV_RunJoin_WeightPointRows46
open Aeneas Aeneas.Std Result
open PV_B2_F_ConstructorCarrier (K amap)
open PV_RunJoin_WeightKernel46 (toQ)
open PV_RunJoin_WeightMap46 (mapResult map_bind)
abbrev Matrix := Array (Array K 4#usize) 5#usize

def remaining (p : Array K 10#usize) : Nat → Matrix → Usize → Result Matrix
  | 0,out,_ => ok out
  | n+1,out,d => do
    let t ← Array.index_usize AspisR1ProducerRelease47.point_rows.TAU d
    let a ← Array.index_usize p (Usize.wrapping_sub 9#usize (Usize.wrapping_mul 2#usize t))
    let b ← Array.index_usize p (Usize.wrapping_sub 8#usize (Usize.wrapping_mul 2#usize t))
    let row ← PV_RunJoin_WeightPointFactor46.run a b
    let out1 ← Array.update out d row
    remaining p n out1 (Usize.wrapping_add d 1#usize)

theorem complete (p : Array K 10#usize) (n : Nat) (out : Matrix)
    (d : Usize) (left : U8) (hl : left.val=n) :
    AspisR1ProducerRelease47.point_rows.fill (amap toQ p) (amap (amap toQ) out) d left=
      mapResult (amap (amap toQ)) (remaining p n out d) := by
  induction n generalizing out d left with
  | zero =>
    have hz : left=0#u8 := by scalar_tac
    subst left
    rw [AspisR1ProducerRelease47.point_rows.fill]
    rfl
  | succ n ih =>
    have hn : left≠0#u8 := by scalar_tac
    have hdec : (U8.wrapping_sub left 1#u8).val=n := by
      rw [U8.wrapping_sub_val_eq,UScalar.size]
      change (left.val+255)%256=n
      have hb := left.hBounds
      change left.val<256 at hb
      omega
    rw [AspisR1ProducerRelease47.point_rows.fill,remaining]
    simp only [if_neg hn,lift,bind_tc_ok,PV_RunJoin_WeightResult46.shared_bind]
    apply (Aeneas.Std.bind_eq_iff _ _ _).mpr
    intro t _
    rw [PV_RunJoin_WeightMap46.index]
    symm
    apply map_bind toQ (amap (amap toQ))
    intro a
    rw [PV_RunJoin_WeightMap46.index]
    apply map_bind toQ (amap (amap toQ))
    intro b
    rw [PV_RunJoin_WeightPointFactor46.complete]
    apply map_bind (amap toQ) (amap (amap toQ))
    intro row
    rw [PV_RunJoin_WeightUpdate46.complete]
    apply map_bind (amap (amap toQ)) (amap (amap toQ))
    intro out1
    exact (ih out1 _ _ hdec).symm
#print axioms complete
end R1Z.PV_RunJoin_WeightPointRows46
