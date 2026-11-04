import NFW_NBQ_Powers29
set_option autoImplicit false
namespace AspisR1.NFW_PowersFrame
open Aeneas Aeneas.Std Result ControlFlow NFN_LPi_FieldValues
/-- The early-return branch has no multiplication domain requirement. -/
theorem final {N : Usize} (a : Array NE N) (p x : NE) (i : Usize)
 (inside : i.val<N.val) (last : i.val+1=N.val) :
 FIo_Native.weights.powers_loop.body x a p i=ok (.done (a.set i p)) := by
 obtain ⟨out,hmut,hspec⟩ := WP.spec_imp_exists
  (Array.index_mut_usize_spec a i (by simpa [a.property] using inside))
 rcases out with ⟨old,back⟩
 rcases hspec with ⟨_,hback⟩
 subst back
 have next : Usize.wrapping_add i 1#usize=N := by
  apply UScalar.eq_of_val_eq
  rw [Usize.wrapping_add_val_eq]
  have hN : N.val<UScalar.size .Usize := by
   simpa only [UScalar.size,UScalar.val,UScalarTy.numBits] using N.bv.isLt
  change (i.val+1)%UScalar.size .Usize=N.val
  rw [last,Nat.mod_eq_of_lt hN]
 have test : i<N := by scalar_tac
 simp only [FIo_Native.weights.powers_loop.body,test,ite_true,hmut,lift,bind_tc_ok,next]
 rfl
/-- Pointwise store/frame laws lift each selected native word observation. -/
theorem frame {N : Usize} (a : Array NE N) (p : NE) (i : Usize) (j : Nat)
 (different : j≠i.val) : (a.set i p).val[j]?=a.val[j]? := by
 simp [Array.set,List.getElem?_set,different,Ne.symm different]
theorem write {N : Usize} (a : Array NE N) (p : NE) (i : Usize)
 (inside : i.val<N.val) : (a.set i p).val[i.val]?=some p := by
 have bound : i.val<a.val.length := by simpa [a.property] using inside
 simp [Array.set,List.getElem?_set,bound,inside]
#print axioms final
#print axioms frame
#print axioms write
end AspisR1.NFW_PowersFrame
