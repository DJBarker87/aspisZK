import Port3_PushFrame

/-! Local R22 facts for bounded release-MIR counters. The extraction uses
wrapping Usize operations; they are not silently identified with checked ones. -/
set_option autoImplicit false
namespace AspisR1.Port3_Wrapping
open Aeneas Aeneas.Std Result

theorem wrap_add_value (x y : Usize) (small : x.val+y.val≤4096) :
    (Usize.wrapping_add x y).val=x.val+y.val := by
  rw [Usize.wrapping_add_val_eq]
  apply Nat.mod_eq_of_lt
  have capacity : 4096<UScalar.size .Usize := by rw [UScalar.size_def]; scalar_tac
  omega

theorem wrap_mul_value (x y : Usize) (small : x.val*y.val≤4096) :
    (Usize.wrapping_mul x y).val=x.val*y.val := by
  rw [Usize.wrapping_mul_val_eq]
  apply Nat.mod_eq_of_lt
  have capacity : 4096<UScalar.size .Usize := by rw [UScalar.size_def]; scalar_tac
  omega

theorem increment (x : Usize) (small : x.val<256) :
    (Usize.wrapping_add x 1#usize).val=x.val+1 := by
  exact wrap_add_value x 1#usize (by change x.val+1≤4096; omega)

theorem checked_add (x y : Usize) (small : x.val+y.val≤4096) :
    (x+y : Result Usize)=ok (Usize.wrapping_add x y) := by
  have capacity : 4096≤Usize.max := by scalar_tac
  have spec : WP.spec (x+y : Result Usize) (fun out => out.val=x.val+y.val) := by
    apply UScalar.add_spec
    simpa only [UScalar.max_USize_eq] using small.trans capacity
  obtain ⟨out,run,value⟩ := WP.spec_imp_exists spec
  have same : out=Usize.wrapping_add x y := by
    apply UScalar.eq_of_val_eq
    exact value.trans (wrap_add_value x y small).symm
  exact run.trans (congrArg Result.ok same)

#print axioms wrap_add_value
#print axioms wrap_mul_value
#print axioms increment
#print axioms checked_add
end AspisR1.Port3_Wrapping
