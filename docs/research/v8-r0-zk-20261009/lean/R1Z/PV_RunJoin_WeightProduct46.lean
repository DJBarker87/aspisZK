import R1Z.PV_RunJoin_WeightQuartic46
set_option autoImplicit false
namespace R1Z.PV_RunJoin_WeightProduct46
open Aeneas Aeneas.Std Result PV_RunJoin_WeightCarrier46
open PV_B2_F_ConstructorCarrier (amap)
open PV_RunJoin_WeightMap46 (mapResult map_bind)

def product (rows : Array (Array Q 4#usize) 5#usize) (j : Usize) :
    Nat → Usize → Q → Result Q
  | 0,_,acc => ok acc
  | n+1,d,acc => do
    let row ← Array.index_usize rows d
    let q ← Array.index_usize row
      (Usize.wrapping_shr j (UScalar.cast .U32 (Usize.wrapping_mul 2#usize d)) &&& 3#usize)
    let next ← PV_B2_251c1.aspis_core.field.QM31.mul acc q
    product rows j n (Usize.wrapping_add d 1#usize) next

theorem complete (rows : Array (Array Q 4#usize) 5#usize) (j : Usize)
    (n : Nat) (d : Usize) (left : U8) (hl : left.val=n) (acc : Q) :
    AspisR1ProducerRelease47.stored.product (amap (amap toQ) rows) j d left (toQ acc)=
      mapResult toQ (product rows j n d acc) := by
  induction n generalizing d left acc with
  | zero =>
    have hz : left=0#u8 := by scalar_tac
    subst left
    rw [AspisR1ProducerRelease47.stored.product]
    rfl
  | succ n ih =>
    have hn : left≠0#u8 := by scalar_tac
    have hdec : (U8.wrapping_sub left 1#u8).val=n := by
      rw [U8.wrapping_sub_val_eq,UScalar.size]
      change (left.val + (256-1))%256=n
      have hb := left.hBounds
      change left.val<256 at hb
      omega
    rw [AspisR1ProducerRelease47.stored.product,product]
    simp only [if_neg hn,lift,bind_tc_ok]
    rw [PV_RunJoin_WeightMap46.index]
    symm
    apply map_bind (amap toQ) toQ
    intro row
    rw [PV_RunJoin_WeightMap46.index]
    apply map_bind toQ toQ
    intro q
    rw [PV_RunJoin_WeightQuartic46.mul]
    apply map_bind toQ toQ
    intro next
    exact (ih _ _ hdec next).symm
#print axioms complete
end R1Z.PV_RunJoin_WeightProduct46
