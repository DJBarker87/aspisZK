import R1Z.PV_RunJoin_WeightCell46
import R1Z.PV_RunJoin_WeightRowArray46
import AspisR1ProducerRelease47.WeightsMaterial53
set_option autoImplicit false
namespace R1Z.PV_RunJoin_WeightFill46
open Aeneas Aeneas.Std Result PV_RunJoin_WeightCarrier46
open PV_RunJoin_WeightWide46 (E toWide)
open PV_B2_F_ConstructorCarrier (amap)
open PV_RunJoin_WeightMap46 (mapResult map_bind)
abbrev Out := Array E 1024#usize

def finite (w : W) (kp : Array E 7#usize) : Nat → Out → Usize → Result Out
  | 0,out,_ => ok out
  | n+1,out,j => do
    let row ← PV_RunJoin_WeightRowArray46.run w j
    let initial ← Array.index_usize out j
    let next ← PV_RunJoin_WeightCell46.finite 7 kp row 0#usize initial
    let out1 ← Array.update out j next
    finite w kp n out1 (Usize.wrapping_add j 1#usize)

theorem complete (w : W) (hs : w.variant=.S2) (kp : Array E 7#usize)
    (n : Nat) (out : Out) (j : Usize) (left : U16) (hl : left.val=n) :
    AspisR1ProducerRelease47.weights_material53.fill (state w) (amap toWide kp)
        (amap toWide out) j left=mapResult (amap toWide) (finite w kp n out j) := by
  induction n generalizing out j left with
  | zero =>
    have hz : left=0#u16 := by scalar_tac
    subst left
    rw [AspisR1ProducerRelease47.weights_material53.fill]
    rfl
  | succ n ih =>
    have hn : left≠0#u16 := by scalar_tac
    have hd : (U16.wrapping_sub left 1#u16).val=n := by
      rw [U16.wrapping_sub_val_eq,UScalar.size]
      change (left.val+65535)%65536=n
      have hb := left.hBounds
      change left.val<65536 at hb
      omega
    rw [AspisR1ProducerRelease47.weights_material53.fill,finite]
    simp only [if_neg hn,lift,bind_tc_ok]
    rw [PV_RunJoin_WeightRowArray46.complete w hs]
    symm
    apply map_bind (amap toQ) (amap toWide)
    intro row
    rw [PV_RunJoin_WeightMap46.index]
    apply map_bind toWide (amap toWide)
    intro initial
    rw [PV_RunJoin_WeightCell46.complete 7 kp row 0#usize 7#u8 rfl initial]
    apply map_bind toWide (amap toWide)
    intro next
    rw [PV_RunJoin_WeightUpdate46.complete]
    apply map_bind (amap toWide) (amap toWide)
    intro out1
    exact (ih out1 _ _ hd).symm
#print axioms complete
end R1Z.PV_RunJoin_WeightFill46
