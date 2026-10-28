import AspisR1ProducerRelease47.Pairs
import R1Z.ProverCommitNativeOps47
import R1Z.ProverCommitArrayIndex25
/-! Finite recursion for the D144 owner; this is not yet an identity of the
shipped chunks_exact/zip loop with that owner. -/
set_option autoImplicit false
namespace R1Z.ProverCommitPairCounter47
open Aeneas Aeneas.Std Result AspisR1ProducerRelease47
open ProverCommitPrimitive47 ProverCommitSubfieldOps47
open ProverCommitNativeOps47
abbrev E := field.wide_exact.WideExact

def finite : Nat → Array E 1024#usize → Array E 512#usize → Usize → E → E → Result (E × E)
 | 0,_,_,_,p0,p1 => ok (p0,p1)
 | n+1,q,basis,i,p0,p1 => do
  let v ← Array.index_usize basis i
  let a ← Array.index_usize q (Std.Usize.wrapping_mul 2#usize i)
  let a ← field.wide_exact.WideExact.mul a v
  let p0 ← field.wide_exact.WideExact.add p0 a
  let b ← Array.index_usize q (Std.Usize.wrapping_add (Std.Usize.wrapping_mul 2#usize i) 1#usize)
  let b ← field.wide_exact.WideExact.mul b v
  let p1 ← field.wide_exact.WideExact.add p1 b
  finite n q basis (Std.Usize.wrapping_add i 1#usize) p0 p1

theorem sub_one (left : U16) (positive : 0<left.val) :
    (U16.wrapping_sub left 1#u16).val=left.val-1 := by
  rw [U16.wrapping_sub_val_eq]
  have one : (1#u16).val=1 := rfl
  rw [one]
  have bound := left.hSize
  have size : 0<UScalar.size .U16 := by rw [UScalar.size_def];positivity
  have shift : left.val+(UScalar.size .U16-1)=(left.val-1)+UScalar.size .U16 := by omega
  rw [shift,Nat.add_mod_right,Nat.mod_eq_of_lt (by omega)]

theorem source_finite (n : Nat) (left : U16) (hleft : left.val=n)
    (q : Array E 1024#usize) (basis : Array E 512#usize) (i : Usize) (p0 p1 : E) :
    pairs q basis i left p0 p1=finite n q basis i p0 p1 := by
  induction n generalizing left i p0 p1 with
  | zero =>
    have hz : left=0#u16 := by scalar_tac
    rw [pairs,hz]
    rfl
  | succ n ih =>
    have hn : left≠0#u16 := by scalar_tac
    have ht : (U16.wrapping_sub left 1#u16).val=n := by rw [sub_one left (by omega)];omega
    rw [pairs]
    simp only [hn,if_false,finite,lift,bind_tc_ok]
    have tail : ∀ a b, pairs q basis (Usize.wrapping_add i 1#usize)
        (U16.wrapping_sub left 1#u16) a b =
        finite n q basis (Usize.wrapping_add i 1#usize) a b :=
      fun a b => ih _ ht _ a b
    simp only [tail]

def sourceArray (n : Usize) (xs : Nat → Old.Q) : Array E n :=
  ⟨List.ofFn (fun i : Fin n.val => ProverCommitNativeOps47.embedded (xs i.val)),by simp⟩

theorem index (n : Usize) (xs : Nat → Old.Q) (i : Usize) (hi : i.val<n.val) :
    Array.index_usize (sourceArray n xs) i = ok (ProverCommitNativeOps47.embedded (xs i.val)) := by
  rw [ProverCommitArrayIndex25.array_index_usize_ok _ _ hi]
  simp only [sourceArray,List.getElem_ofFn]

theorem usize_large : 2048<UScalar.size .Usize := by
  have h : 2^32 ≤ UScalar.size .Usize := by
    rw [UScalar.size_def]
    exact Nat.pow_le_pow_right (by decide) System.Platform.le_numBits
  norm_num at h ⊢
  omega

theorem double_val (i : Usize) (hi : i.val<512) :
    (Usize.wrapping_mul 2#usize i).val=2*i.val := by
  rw [Usize.wrapping_mul_val_eq]
  have two : (2#usize).val=2 := by scalar_tac
  rw [two]
  exact Nat.mod_eq_of_lt (by have := usize_large;omega)

theorem next_val (i : Usize) (hi : i.val<1024) :
    (Usize.wrapping_add i 1#usize).val=i.val+1 := by
  rw [Usize.wrapping_add_val_eq]
  have one : (1#usize).val=1 := by scalar_tac
  rw [one]
  exact Nat.mod_eq_of_lt (by have := usize_large;omega)

theorem odd_val (i : Usize) (hi : i.val<512) :
    (Usize.wrapping_add (Usize.wrapping_mul 2#usize i) 1#usize).val=2*i.val+1 := by
  rw [next_val _ (by rw [double_val i hi];omega),double_val i hi]

#print axioms usize_large
#print axioms double_val
#print axioms next_val
#print axioms odd_val
#print axioms sub_one
#print axioms source_finite
#print axioms index
end R1Z.ProverCommitPairCounter47
