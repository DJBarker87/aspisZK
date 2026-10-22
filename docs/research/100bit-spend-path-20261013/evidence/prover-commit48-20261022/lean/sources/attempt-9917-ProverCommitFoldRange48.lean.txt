import R1Z.ProverCommitFoldCell48
import R1Z.ProverCommitWideArray48
import R1Z.ProverCommitBasisFillValue47
/-! Finite forward denotation of both primal fold passes. Bounds and source
array failures are retained; no concrete 256/64-step kernel evaluation. -/
set_option autoImplicit false
namespace R1Z.ProverCommitFoldRange48
open Aeneas Aeneas.Std Result AspisR1ProducerRelease47
open ProverCommitWideOps48 ProverCommitMix48

def range (inputSize outputSize : Usize) : Nat → Array Source inputSize → Source →
    Array Source outputSize → Usize → Result (Array Source outputSize)
 | 0,_,_,out,_ => ok out
 | n+1,q,a,out,i => do
  let v0 ← Array.index_usize q (Usize.wrapping_mul 4#usize i)
  let v1 ← Array.index_usize q (Usize.wrapping_add (Usize.wrapping_mul 4#usize i) 1#usize)
  let v2 ← Array.index_usize q (Usize.wrapping_add (Usize.wrapping_mul 4#usize i) 2#usize)
  let v3 ← Array.index_usize q (Usize.wrapping_add (Usize.wrapping_mul 4#usize i) 3#usize)
  let z ← fold_cell (Array.make 4#usize [v0,v1,v2,v3]) a
  let out ← Array.update out i z
  range inputSize outputSize n q a out (Usize.wrapping_add i 1#usize)

theorem first_source (n : Nat) (left : U16) (hleft : left.val=n)
    (q : Array Source 1024#usize) (a : Source) (out : Array Source 256#usize) (i : Usize) :
    fold_first q a out i left=range 1024#usize 256#usize n q a out i := by
  induction n generalizing left out i with
  | zero =>
    have hz : left=0#u16 := by scalar_tac
    rw [fold_first,hz]
    rfl
  | succ n ih =>
    have hn : left≠0#u16 := by scalar_tac
    have ht : (U16.wrapping_sub left 1#u16).val=n := by
      rw [ProverCommitPairCounter47.sub_one left (by omega)]
      omega
    rw [fold_first]
    simp only [hn,if_false,range,lift,bind_tc_ok]
    have tail : ∀ v, fold_first q a v (Usize.wrapping_add i 1#usize)
        (U16.wrapping_sub left 1#u16)=range 1024#usize 256#usize n q a v (Usize.wrapping_add i 1#usize) :=
      fun v => ih _ ht v _
    simp only [tail]

theorem second_source (n : Nat) (left : U8) (hleft : left.val=n)
    (q : Array Source 256#usize) (a : Source) (out : Array Source 64#usize) (i : Usize) :
    fold_second q a out i left=range 256#usize 64#usize n q a out i := by
  induction n generalizing left out i with
  | zero =>
    have hz : left=0#u8 := by scalar_tac
    rw [fold_second,hz]
    rfl
  | succ n ih =>
    have hn : left≠0#u8 := by scalar_tac
    have ht : (U8.wrapping_sub left 1#u8).val=n := by
      rw [ProverCommitBasisCounter47.sub_one left (by omega)]
      omega
    rw [fold_second]
    simp only [hn,if_false,range,lift,bind_tc_ok]
    have tail : ∀ v, fold_second q a v (Usize.wrapping_add i 1#usize)
        (U8.wrapping_sub left 1#u8)=range 256#usize 64#usize n q a v (Usize.wrapping_add i 1#usize) :=
      fun v => ih _ ht v _
    simp only [tail]

theorem four_val (i : Usize) (hi : i.val<256) :
    (Usize.wrapping_mul 4#usize i).val=4*i.val := by
  rw [Usize.wrapping_mul_val_eq]
  have four : (4#usize).val=4 := by scalar_tac
  rw [four]
  exact Nat.mod_eq_of_lt (by have := ProverCommitPairCounter47.usize_large;omega)

theorem offset_val (i : Usize) (hi : i.val<256) (offset : Usize) (ho : offset.val≤3) :
    (Usize.wrapping_add (Usize.wrapping_mul 4#usize i) offset).val=4*i.val+offset.val := by
  rw [ProverCommitBasisFillValue47.add_val _ _ (by rw [four_val i hi];omega),four_val i hi]

theorem four_array (q : Nat → Raw) :
    Array.make 4#usize [source (q 0),source (q 1),source (q 2),source (q 3)]=sourceArray 4#usize q := by
  apply Subtype.ext
  simp only [Array.make,sourceArray,List.ofFn_succ,List.ofFn_zero]
  rfl

#print axioms first_source
#print axioms second_source
#print axioms four_val
#print axioms offset_val
#print axioms four_array
end R1Z.ProverCommitFoldRange48
