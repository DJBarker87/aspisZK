import NNU_MerkleLevels
set_option autoImplicit false
namespace AspisR1.NNU_MerkleRoot
open Aeneas Aeneas.Std Result MultiproofConeRef

theorem final (root : Array U8 32#usize) (physical : Slice U8) (out : reference.Scratch)
 (guard : MultiproofConeRootGuard.sourceRoot root physical out=true) :
 (do
   if out.n=1#usize then
    let i ← Array.index_usize out.idx 0#usize
    if i=0#u32 then
     let v ← Array.index_usize out.val 0#usize
     let same ← core.array.equality.PartialEqArray.eq core.cmp.PartialEqU8 v root
     if same then .ok (out.«at»=Slice.len physical,out) else .ok (false,out)
    else .ok (false,out)
   else .ok (false,out)) = .ok (true,out) := by
 have facts := of_decide_eq_true guard
 change out.n.val=1 ∧ out.idx.val[0]!.val=0 ∧ out.val.val[0]! = root ∧ out.«at».val=physical.val.length at facts
 have one : out.n=1#usize := UScalar.eq_of_val_eq facts.1
 have index : out.idx.val[0]! = 0#u32 := UScalar.eq_of_val_eq facts.2.1
 have cursor : out.«at»=Slice.len physical := UScalar.eq_of_val_eq facts.2.2.2
 simp only [one,if_true,MultiproofConePhysicalPrelude.array_read out.idx 0#usize (by decide),
  MultiproofConePhysicalPrelude.array_read out.val 0#usize (by decide),bind_tc_ok,index,facts.2.2.1,
  MultiproofConeLeaf.digest_eq_total,decide_true,cursor,decide_true]
#print axioms final
end AspisR1.NNU_MerkleRoot
