import R1Z.PV_RunJoin_WeightKernel46
import R1Z.PV_RunJoin_WeightUpdate46
import AspisR1ProducerRelease47.Points49
set_option autoImplicit false
namespace R1Z.PV_RunJoin_WeightSuccessor46
open Aeneas Aeneas.Std Result
open PV_B2_F_ConstructorCarrier (K amap)
open PV_RunJoin_WeightKernel46 (toQ)
open PV_RunJoin_WeightMap46 (mapResult map_bind)

def remaining (p : Array K 10#usize) :
    Nat → Array K 10#usize → U8 → K → Result (Array K 10#usize)
  | 0,out,_,_ => ok out
  | n+1,out,left,carry => do
    let coordinate := UScalar.cast .Usize (U8.wrapping_sub left 1#u8)
    let bit ← Array.index_usize p coordinate
    let bc ← PV_B2_C_WeightsNative.aspis_core.field.QM31.mul bit carry
    let q ← PV_B2_C_WeightsNative.aspis_core.field.QM31.add bit carry
    let q1 ← PV_B2_C_WeightsNative.aspis_core.field.QM31.add bc bc
    let q2 ← PV_B2_C_WeightsNative.aspis_core.field.QM31.sub q q1
    let out1 ← Array.update out coordinate q2
    remaining p n out1 (U8.wrapping_sub left 1#u8) bc

theorem complete (p : Array K 10#usize) (n : Nat) (out : Array K 10#usize)
    (left : U8) (carry : K) (hl : left.val=n) :
    AspisR1ProducerRelease47.points.successor (amap toQ p) (amap toQ out) left (toQ carry)=
      mapResult (amap toQ) (remaining p n out left carry) := by
  induction n generalizing out left carry with
  | zero =>
    have hz : left=0#u8 := by scalar_tac
    subst left
    rw [AspisR1ProducerRelease47.points.successor]
    rfl
  | succ n ih =>
    have hn : left≠0#u8 := by scalar_tac
    have hdec : (U8.wrapping_sub left 1#u8).val=n := by
      rw [U8.wrapping_sub_val_eq,UScalar.size]
      change (left.val+255)%256=n
      have hb := left.hBounds
      change left.val<256 at hb
      omega
    rw [AspisR1ProducerRelease47.points.successor,remaining]
    simp only [if_neg hn,lift,bind_tc_ok,PV_RunJoin_WeightMap46.index]
    symm
    apply map_bind toQ (amap toQ)
    intro bit
    rw [PV_RunJoin_WeightKernel46.mul]
    apply map_bind toQ (amap toQ)
    intro bc
    rw [PV_RunJoin_WeightKernel46.add]
    apply map_bind toQ (amap toQ)
    intro q
    rw [PV_RunJoin_WeightKernel46.add]
    apply map_bind toQ (amap toQ)
    intro q1
    rw [PV_RunJoin_WeightKernel46.sub]
    apply map_bind toQ (amap toQ)
    intro q2
    rw [PV_RunJoin_WeightUpdate46.complete]
    apply map_bind (amap toQ) (amap toQ)
    intro out1
    exact (ih out1 _ bc hdec).symm
#print axioms complete
end R1Z.PV_RunJoin_WeightSuccessor46
