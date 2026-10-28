import R1Z.PV_RunJoin_WeightPointRows46
import R1Z.ProverCommitArrayIndex25
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
  exact PV_RunJoin_WeightBorrow46.complete fs slot
    (fun m back => do let m1 ← Array.update m d row;ok (back m1))
#print axioms equation

theorem read_set (fs : Factors) (slot : Usize) (m : Matrix) (hs : slot.val<5) :
    Array.index_usize (Aeneas.Std.Array.set fs slot m) slot=ok m := by
  rw [ProverCommitArrayIndex25.array_index_usize_ok _ _ (by scalar_tac)]
  apply congrArg Result.ok
  change (fs.val.set slot.val m)[slot.val]'_=m
  exact List.getElem_set_self (by rw [List.length_set,fs.property];exact hs)
#print axioms read_set

theorem overwrite (fs : Factors) (slot : Usize) (m m1 : Matrix) :
    Aeneas.Std.Array.set (Aeneas.Std.Array.set fs slot m) slot m1=
      Aeneas.Std.Array.set fs slot m1 := by
  apply Subtype.ext
  change (fs.val.set slot.val m).set slot.val m1=fs.val.set slot.val m1
  simp only [List.set_set]
#print axioms overwrite
end R1Z.PV_RunJoin_WeightFactorWrite47
