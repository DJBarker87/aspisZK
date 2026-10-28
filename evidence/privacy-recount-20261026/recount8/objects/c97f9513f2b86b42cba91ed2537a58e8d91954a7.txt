import AspisR1ProducerRelease47.Basis
import R1Z.ProverCommitPairCounter47
/-! Symbolic finite counters for the D144 basis owner. Neither array values
nor native/source-loop equality is inferred from the fuel equations. -/
set_option autoImplicit false
namespace R1Z.ProverCommitBasisCounter47
open Aeneas Aeneas.Std Result AspisR1ProducerRelease47
abbrev E := field.wide_exact.WideExact

def fillN : Nat → Array E 512#usize → Usize → Usize → E → Result (Array E 512#usize)
 | 0,out,_,_,_ => ok out
 | n+1,out,j,width,factor => do
  let v ← Array.index_usize out j
  let product ← field.wide_exact.WideExact.mul v factor
  let out ← Array.update out (Usize.wrapping_add width j) product
  fillN n out (Usize.wrapping_add j 1#usize) width factor

theorem fill_source (n : Nat) (left : U16) (hleft : left.val=n)
    (out : Array E 512#usize) (j width : Usize) (factor : E) :
    fill out j left width factor=fillN n out j width factor := by
  induction n generalizing left out j with
  | zero =>
    have hz : left=0#u16 := by scalar_tac
    rw [fill,hz]
    rfl
  | succ n ih =>
    have hn : left≠0#u16 := by scalar_tac
    have ht : (U16.wrapping_sub left 1#u16).val=n := by
      rw [ProverCommitPairCounter47.sub_one left (by omega)]
      omega
    rw [fill]
    simp only [hn,if_false,fillN,lift,bind_tc_ok]
    have tail : ∀ a, fill a (Usize.wrapping_add j 1#usize)
        (U16.wrapping_sub left 1#u16) width factor =
        fillN n a (Usize.wrapping_add j 1#usize) width factor := fun a => ih _ ht a _
    simp only [tail]

def stagesN : Nat → Array E 512#usize → Usize → E → Result (Array E 512#usize)
 | 0,out,_,_ => ok out
 | n+1,out,width,factor => do
  let out ← fill out 0#usize (UScalar.cast .U16 width) width factor
  let square ← field.wide_exact.WideExact.mul factor factor
  let twice ← field.wide_exact.WideExact.add square square
  let next ← field.wide_exact.WideExact.sub twice field.wide_exact.WideExact.ONE
  stagesN n out (Usize.wrapping_mul width 2#usize) next

theorem sub_one (left : U8) (positive : 0<left.val) :
    (U8.wrapping_sub left 1#u8).val=left.val-1 := by
  rw [U8.wrapping_sub_val_eq]
  have one : (1#u8).val=1 := rfl
  rw [one]
  have bound := left.hSize
  have size : 0<UScalar.size .U8 := by rw [UScalar.size_def];positivity
  have shift : left.val+(UScalar.size .U8-1)=(left.val-1)+UScalar.size .U8 := by omega
  rw [shift,Nat.add_mod_right,Nat.mod_eq_of_lt (by omega)]

theorem stages_source (n : Nat) (left : U8) (hleft : left.val=n)
    (out : Array E 512#usize) (width : Usize) (factor : E) :
    stages out left width factor=stagesN n out width factor := by
  induction n generalizing left out width factor with
  | zero =>
    have hz : left=0#u8 := by scalar_tac
    rw [stages,hz]
    rfl
  | succ n ih =>
    have hn : left≠0#u8 := by scalar_tac
    have ht : (U8.wrapping_sub left 1#u8).val=n := by rw [sub_one left (by omega)];omega
    rw [stages]
    simp only [hn,if_false,stagesN,lift,bind_tc_ok]
    have tail : ∀ a f, stages a (U8.wrapping_sub left 1#u8)
        (Usize.wrapping_mul width 2#usize) f =
        stagesN n a (Usize.wrapping_mul width 2#usize) f := fun a f => ih _ ht a _ f
    simp only [tail]

theorem values_counter (x : E) :
    values x=stagesN 9 (Array.repeat 512#usize field.wide_exact.WideExact.ONE) 1#usize x := by
  rw [values,stages_source 9 _ rfl]

#print axioms fill_source
#print axioms sub_one
#print axioms stages_source
#print axioms values_counter
end R1Z.ProverCommitBasisCounter47
