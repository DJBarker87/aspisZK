import R1Z.PV_RunJoin_WeightScale46
import R1Z.PV_RunJoin_WeightUpdate46
set_option autoImplicit false
namespace R1Z.PV_RunJoin_WeightCell46
open Aeneas Aeneas.Std Result PV_RunJoin_WeightCarrier46
open PV_RunJoin_WeightWide46 (E toWide)
open PV_B2_F_ConstructorCarrier (amap)
open PV_RunJoin_WeightMap46 (mapResult map_bind)

def finite : Nat → Array E 7#usize → Array Q 7#usize → Usize → E → Result E
  | 0,_,_,_,sum => ok sum
  | n+1,kp,raw,kind,sum => do
    let x ← Array.index_usize kp kind
    let q ← Array.index_usize raw kind
    let product ← PV_B2_251c1.host_weights.mul_qm31 x q
    let next ← PV_B2_251c1.aspis_core.field.wide_exact.WideExact.add sum product
    finite n kp raw (Usize.wrapping_add kind 1#usize) next

theorem complete (n : Nat) (kp : Array E 7#usize) (raw : Array Q 7#usize)
    (kind : Usize) (left : U8) (hl : left.val=n) (sum : E) :
    AspisR1ProducerRelease47.owned.cell (amap toWide kp) (amap toQ raw) kind left (toWide sum)=
      mapResult toWide (finite n kp raw kind sum) := by
  induction n generalizing kind left sum with
  | zero =>
    have hz : left=0#u8 := by scalar_tac
    subst left
    rw [AspisR1ProducerRelease47.owned.cell]
    rfl
  | succ n ih =>
    have hn : left≠0#u8 := by scalar_tac
    have hd : (U8.wrapping_sub left 1#u8).val=n := by
      rw [U8.wrapping_sub_val_eq,UScalar.size]
      change (left.val+255)%256=n
      have hb := left.hBounds
      change left.val<256 at hb
      omega
    rw [AspisR1ProducerRelease47.owned.cell,finite]
    simp only [if_neg hn,lift,bind_tc_ok]
    rw [PV_RunJoin_WeightMap46.index]
    symm
    apply map_bind toWide toWide
    intro x
    rw [PV_RunJoin_WeightMap46.index]
    apply map_bind toQ toWide
    intro q
    rw [PV_RunJoin_WeightScale46.complete]
    apply map_bind toWide toWide
    intro product
    rw [PV_RunJoin_WeightWide46.add]
    apply map_bind toWide toWide
    intro next
    exact (ih _ _ hd next).symm
#print axioms complete
end R1Z.PV_RunJoin_WeightCell46
