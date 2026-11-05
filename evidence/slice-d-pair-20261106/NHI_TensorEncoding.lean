import NHI_TensorRefLaw
import NHI_WordEncoding
set_option autoImplicit false
noncomputable section
namespace NHI_TensorEncoding
open Aeneas Aeneas.Std Result AspisR1 LPi_FieldValues
open NHI_WordEncoding

def products (input : Slice NQ) (j : Nat) (row : Array NQ 4#usize) : NHI_TensorRefLaw.Products :=
 let x := NHI_QProduct.sliceAt input j
 Array.make 4#usize [words (NHI_QProduct.mul x (NHI_QProduct.arrayAt row 0)),
  words (NHI_QProduct.mul x (NHI_QProduct.arrayAt row 1)),
  words (NHI_QProduct.mul x (NHI_QProduct.arrayAt row 2)),
  words (NHI_QProduct.mul x (NHI_QProduct.arrayAt row 3))]

theorem length (input : Slice NQ) (j n : Nat) (row : Array NQ 4#usize) :
 (NHI_TensorExactCell.place input j n row).val.length=input.val.length := by
 simp only [NHI_TensorExactCell.place,NHI_SliceCells.put,List.length_set]

/-- The compiled owned reference is the exact word encoding of the emitted
cell's four-product update, including the entire disjoint frame. -/
theorem window (input : Slice NQ) (row : Array NQ 4#usize) (j n : Usize)
 (size : input.val.length=64) (hn : NHI_TensorDomains.Stage n.val) (hj : j.val<n.val) :
 NHE_TensorRef.tensor_ref (array input size) j n (products input j.val row)=
 ok (array (NHI_TensorExactCell.place input j.val n.val row) ((length input j.val n.val row).trans size)) := by
 rw [NHI_TensorRefLaw.source _ _ j n hn hj]
 congr 1
 apply Subtype.ext
 have cap : 4096<UScalar.size .Usize := by rw [UScalar.size_def];scalar_tac
 have small : j.val+n.val<UScalar.size .Usize := by rcases hn with h|h|h <;> omega
 have v1 : (Usize.wrapping_add j n).val=j.val+n.val := by
  rw [Usize.wrapping_add_val_eq,Nat.mod_eq_of_lt small]
 have v2 := (NHI_TensorOffsets.value n j 2#usize hn hj (by decide)).1
 have v3 := (NHI_TensorOffsets.value n j 3#usize hn hj (by decide)).1
 change (NHI_TensorOffsets.index j n 2#usize).val=j.val+2*n.val at v2
 change (NHI_TensorOffsets.index j n 3#usize).val=j.val+3*n.val at v3
 simp only [NHI_TensorRefLaw.place,NHI_ArrayCells.put,array]
 rw [v1,v2,v3]
 simp only [NHI_TensorRefLaw.cell,NHI_ScalarDomain.pick,products,Array.make,
  NHI_TensorExactCell.place,NHI_SliceCells.put,List.map_set] <;> rfl

#print axioms length
#print axioms window
end NHI_TensorEncoding
end
