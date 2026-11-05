import NHI_ArrayCells
import NHI_TensorOffsets
import NHI_TensorExtracted
set_option autoImplicit false
namespace NHI_TensorRefLaw
open Aeneas Aeneas.Std Result
abbrev Word := Array U32 4#usize
abbrev Output := Array Word 64#usize
abbrev Products := Array Word 4#usize

def cell (p : Products) (i : Fin 4) : Word := NHI_ScalarDomain.pick p i.val i.isLt

def place (out : Output) (p : Products) (j n : Usize) : Output :=
 NHI_ArrayCells.put (NHI_ArrayCells.put (NHI_ArrayCells.put
  (NHI_ArrayCells.put out j (cell p 0)) (Usize.wrapping_add j n) (cell p 1))
  (NHI_TensorOffsets.index j n 2#usize) (cell p 2))
  (NHI_TensorOffsets.index j n 3#usize) (cell p 3)

/-- Extracted reference equals the exact four opaque-result writes on the
entire arbitrary 64-cell prestate. No field product is assumed or computed. -/
theorem source (out : Output) (p : Products) (j n : Usize)
 (hn : NHI_TensorDomains.Stage n.val) (hj : j.val<n.val) :
 NHE_TensorRef.tensor_ref out j n p=ok (place out p j n) := by
 have size : 4096<UScalar.size .Usize := by rw [UScalar.size_def];scalar_tac
 have ncap : n.val<UScalar.size .Usize := by rcases hn with h|h|h <;> omega
 have one : Usize.wrapping_mul 1#usize n=n := by
  apply UScalar.eq_of_val_eq
  rw [Usize.wrapping_mul_val_eq]
  change n.val%UScalar.size .Usize=n.val
  exact Nat.mod_eq_of_lt ncap
 have off1 := NHI_TensorOffsets.value n j 1#usize hn hj (by decide)
 simp only [NHI_TensorOffsets.index,one] at off1
 have off2 := NHI_TensorOffsets.value n j 2#usize hn hj (by decide)
 have off3 := NHI_TensorOffsets.value n j 3#usize hn hj (by decide)
 have jb : j.val<64 := by rcases hn with h|h|h <;> omega
 have r0 := NHI_ScalarDomain.index p 0#usize (by decide)
 have r1 := NHI_ScalarDomain.index p 1#usize (by decide)
 have r2 := NHI_ScalarDomain.index p 2#usize (by decide)
 have r3 := NHI_ScalarDomain.index p 3#usize (by decide)
 let a := NHI_ArrayCells.put out j (cell p 0)
 let b := NHI_ArrayCells.put a (Usize.wrapping_add j n) (cell p 1)
 let c := NHI_ArrayCells.put b (NHI_TensorOffsets.index j n 2#usize) (cell p 2)
 have u0 := NHI_ArrayCells.update out j (cell p 0) jb
 have u1 := NHI_ArrayCells.update a (Usize.wrapping_add j n) (cell p 1) off1.2
 have u2 := NHI_ArrayCells.update b (NHI_TensorOffsets.index j n 2#usize) (cell p 2) off2.2
 have u3 := NHI_ArrayCells.update c (NHI_TensorOffsets.index j n 3#usize) (cell p 3) off3.2
 change Array.index_usize p 0#usize=ok (cell p 0) at r0
 change Array.index_usize p 1#usize=ok (cell p 1) at r1
 change Array.index_usize p 2#usize=ok (cell p 2) at r2
 change Array.index_usize p 3#usize=ok (cell p 3) at r3
 unfold NHE_TensorRef.tensor_ref
 simp only [r0,r1,r2,r3,lift,bind_tc_ok,u0,u1,u2,u3]
 rfl

#print axioms source
end NHI_TensorRefLaw
