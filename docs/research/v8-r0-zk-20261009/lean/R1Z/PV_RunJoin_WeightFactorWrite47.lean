import R1Z.PV_RunJoin_WeightPointRows46
import R1Z.PV_RunJoin_WeightBorrow46
import R1Z.PV_RunJoin_WeightConstructorShape46
set_option autoImplicit false
namespace R1Z.PV_RunJoin_WeightFactorWrite47
open Aeneas Aeneas.Std Result
open PV_B2_C_ConstructorRows (Factors)
open PV_B2_F_ConstructorCarrier (K)
abbrev Matrix := Array (Array K 4#usize) 5#usize

def write (fs : Factors) (slot d : Usize) (row : Array K 4#usize) : Result Factors := do
  let (m,back) ← Array.index_mut_usize fs slot
  let m1 ← Array.update m d row
  ok (back m1)

theorem equation (fs : Factors) (slot d : Usize) (row : Array K 4#usize) :
    write fs slot d row=(do
      let m ← Array.index_usize fs slot
      let m1 ← Array.update m d row
      ok (Aeneas.Std.Array.set fs slot m1)) := by
  unfold write
  rw [PV_RunJoin_WeightBorrow46.complete]
#print axioms equation

theorem read_set (fs : Factors) (slot : Usize) (m : Matrix) (hs : slot.val<5) :
    Array.index_usize (Aeneas.Std.Array.set fs slot m) slot=ok m := by
  unfold Array.index_usize
  have hb : slot.val<fs.val.length := by rw [fs.property];exact hs
  simp only [Array.getElem?_Usize_eq,Array.set,List.getElem?_set_self hb]
#print axioms read_set

theorem overwrite (fs : Factors) (slot : Usize) (m m1 : Matrix) :
    Aeneas.Std.Array.set (Aeneas.Std.Array.set fs slot m) slot m1=
      Aeneas.Std.Array.set fs slot m1 := by
  apply Subtype.ext
  simp only [Array.set,List.set_set]
#print axioms overwrite
end R1Z.PV_RunJoin_WeightFactorWrite47
