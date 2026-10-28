import R1Z.PV_RunJoin_WeightCircleFactor46
import R1Z.PV_RunJoin_WeightLineFactor46
import R1Z.PV_RunJoin_WeightDoubleFactor46
import R1Z.PV_RunJoin_WeightUpdate46
set_option autoImplicit false
namespace R1Z.PV_RunJoin_WeightCircleRows46
open Aeneas Aeneas.Std Result
open PV_B2_F_ConstructorCarrier (K amap)
open PV_RunJoin_WeightKernel46 (toQ)
open PV_RunJoin_WeightMap46 (mapResult map_bind)
abbrev Matrix := Array (Array K 4#usize) 5#usize

def remaining : Nat → Matrix → Usize → K → Result Matrix
  | 0,out,_,_ => ok out
  | n+1,out,d,x => do
    let y ← PV_RunJoin_WeightDoubleFactor46.run x
    let row ← PV_RunJoin_WeightLineFactor46.run x y
    let out1 ← Array.update out d row
    let next ← PV_RunJoin_WeightDoubleFactor46.run y
    remaining n out1 (Usize.wrapping_add d 1#usize) next

theorem complete (n : Nat) (out : Matrix) (d : Usize) (left : U8) (x : K)
    (hl : left.val=n) :
    AspisR1ProducerRelease47.factors.lines (amap (amap toQ) out) d left (toQ x)=
      mapResult (amap (amap toQ)) (remaining n out d x) := by
  induction n generalizing out d left x with
  | zero =>
    have hz : left=0#u8 := by scalar_tac
    subst left
    rw [AspisR1ProducerRelease47.factors.lines]
    rfl
  | succ n ih =>
    have hn : left≠0#u8 := by scalar_tac
    have hdec : (U8.wrapping_sub left 1#u8).val=n := by
      rw [U8.wrapping_sub_val_eq,UScalar.size]
      change (left.val+255)%256=n
      have hb := left.hBounds
      change left.val<256 at hb
      omega
    rw [AspisR1ProducerRelease47.factors.lines,remaining]
    simp only [if_neg hn,lift,bind_tc_ok]
    symm
    rw [PV_RunJoin_WeightDoubleFactor46.complete]
    apply map_bind toQ (amap (amap toQ))
    intro y
    rw [PV_RunJoin_WeightLineFactor46.complete]
    apply map_bind (amap toQ) (amap (amap toQ))
    intro row
    rw [PV_RunJoin_WeightUpdate46.complete]
    apply map_bind (amap (amap toQ)) (amap (amap toQ))
    intro out1
    rw [PV_RunJoin_WeightDoubleFactor46.complete]
    apply map_bind toQ (amap (amap toQ))
    intro next
    exact (ih out1 _ _ next hdec).symm
#print axioms complete
end R1Z.PV_RunJoin_WeightCircleRows46
